-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:23.317968+00:00
-- url     : https://prove2.me/submissions/b4967906-1996-4c67-bb96-bfd4087780cd

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
theorem support_rectangle_w1285_s6_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-523562299/2500000000 : ℝ)*x 0 + (5415685341/10000000000 : ℝ)*x 1 + (5242648293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523562299/2500000000 : ℝ)^4245 ≤ (6370066709839/50000000000000 : ℝ)^3221 := by
    have hnat : (523562299 : ℕ)^4245*50000000000000^3221 ≤ 6370066709839^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523562299 2500000000 6370066709839 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415685341/10000000000 : ℝ)^4245 ≤ (11140846963153/25000000000000 : ℝ)^3221 := by
    have hnat : (5415685341 : ℕ)^4245*25000000000000^3221 ≤ 11140846963153^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415685341 10000000000 11140846963153 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242648293/10000000000 : ℝ)^4245 ≤ (853929574089/2000000000000 : ℝ)^3221 := by
    have hnat : (5242648293 : ℕ)^4245*2000000000000^3221 ≤ 853929574089^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242648293 10000000000 853929574089 2000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-523562299/2500000000 : ℝ), (5415685341/10000000000 : ℝ), (5242648293/10000000000 : ℝ)] ![(6370066709839/50000000000000 : ℝ), (11140846963153/25000000000000 : ℝ), (853929574089/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-523562299/2500000000 : ℝ)|^4245 ≤ (6370066709839/50000000000000 : ℝ)^3221
        have hw : |(-523562299/2500000000 : ℝ)|=(523562299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415685341/10000000000 : ℝ)|^4245 ≤ (11140846963153/25000000000000 : ℝ)^3221
        have hw : |(5415685341/10000000000 : ℝ)|=(5415685341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242648293/10000000000 : ℝ)|^4245 ≤ (853929574089/2000000000000 : ℝ)^3221
        have hw : |(5242648293/10000000000 : ℝ)|=(5242648293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349909603/10000000000 : ℝ)*x 0 + (-2182462151/10000000000 : ℝ)*x 1 + (5242648291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349909603/10000000000 : ℝ)^4245 ≤ (43851460160219/100000000000000 : ℝ)^3221 := by
    have hnat : (5349909603 : ℕ)^4245*100000000000000^3221 ≤ 43851460160219^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349909603 10000000000 43851460160219 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182462151/10000000000 : ℝ)^4245 ≤ (672603057027/5000000000000 : ℝ)^3221 := by
    have hnat : (2182462151 : ℕ)^4245*5000000000000^3221 ≤ 672603057027^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182462151 10000000000 672603057027 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242648291/10000000000 : ℝ)^4245 ≤ (42696478682983/100000000000000 : ℝ)^3221 := by
    have hnat : (5242648291 : ℕ)^4245*100000000000000^3221 ≤ 42696478682983^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242648291 10000000000 42696478682983 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349909603/10000000000 : ℝ), (-2182462151/10000000000 : ℝ), (5242648291/10000000000 : ℝ)] ![(43851460160219/100000000000000 : ℝ), (672603057027/5000000000000 : ℝ), (42696478682983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349909603/10000000000 : ℝ)|^4245 ≤ (43851460160219/100000000000000 : ℝ)^3221
        have hw : |(5349909603/10000000000 : ℝ)|=(5349909603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182462151/10000000000 : ℝ)|^4245 ≤ (672603057027/5000000000000 : ℝ)^3221
        have hw : |(-2182462151/10000000000 : ℝ)|=(2182462151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242648291/10000000000 : ℝ)|^4245 ≤ (42696478682983/100000000000000 : ℝ)^3221
        have hw : |(5242648291/10000000000 : ℝ)|=(5242648291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674954811/5000000000 : ℝ)*x 0 + (524264827/1000000000 : ℝ)*x 1 + (-1091231077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674954811/5000000000 : ℝ)^4245 ≤ (43851460365467/100000000000000 : ℝ)^3221 := by
    have hnat : (2674954811 : ℕ)^4245*100000000000000^3221 ≤ 43851460365467^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674954811 5000000000 43851460365467 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524264827/1000000000 : ℝ)^4245 ≤ (21348239228793/50000000000000 : ℝ)^3221 := by
    have hnat : (524264827 : ℕ)^4245*50000000000000^3221 ≤ 21348239228793^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524264827 1000000000 21348239228793 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091231077/5000000000 : ℝ)^4245 ≤ (13452061164909/100000000000000 : ℝ)^3221 := by
    have hnat : (1091231077 : ℕ)^4245*100000000000000^3221 ≤ 13452061164909^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091231077 5000000000 13452061164909 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674954811/5000000000 : ℝ), (524264827/1000000000 : ℝ), (-1091231077/5000000000 : ℝ)] ![(43851460365467/100000000000000 : ℝ), (21348239228793/50000000000000 : ℝ), (13452061164909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674954811/5000000000 : ℝ)|^4245 ≤ (43851460365467/100000000000000 : ℝ)^3221
        have hw : |(2674954811/5000000000 : ℝ)|=(2674954811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524264827/1000000000 : ℝ)|^4245 ≤ (21348239228793/50000000000000 : ℝ)^3221
        have hw : |(524264827/1000000000 : ℝ)|=(524264827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091231077/5000000000 : ℝ)|^4245 ≤ (13452061164909/100000000000000 : ℝ)^3221
        have hw : |(-1091231077/5000000000 : ℝ)|=(1091231077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341742543/10000000000 : ℝ)*x 0 + (52098437/125000000 : ℝ)*x 1 + (4522556231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341742543/10000000000 : ℝ)^4245 ≤ (16651084218871/50000000000000 : ℝ)^3221 := by
    have hnat : (4341742543 : ℕ)^4245*50000000000000^3221 ≤ 16651084218871^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341742543 10000000000 16651084218871 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52098437/125000000 : ℝ)^4245 ≤ (31555884262851/100000000000000 : ℝ)^3221 := by
    have hnat : (52098437 : ℕ)^4245*100000000000000^3221 ≤ 31555884262851^3221*125000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52098437 125000000 31555884262851 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522556231/10000000000 : ℝ)^4245 ≤ (35141947275971/100000000000000 : ℝ)^3221 := by
    have hnat : (4522556231 : ℕ)^4245*100000000000000^3221 ≤ 35141947275971^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522556231 10000000000 35141947275971 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341742543/10000000000 : ℝ), (52098437/125000000 : ℝ), (4522556231/10000000000 : ℝ)] ![(16651084218871/50000000000000 : ℝ), (31555884262851/100000000000000 : ℝ), (35141947275971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341742543/10000000000 : ℝ)|^4245 ≤ (16651084218871/50000000000000 : ℝ)^3221
        have hw : |(4341742543/10000000000 : ℝ)|=(4341742543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52098437/125000000 : ℝ)|^4245 ≤ (31555884262851/100000000000000 : ℝ)^3221
        have hw : |(52098437/125000000 : ℝ)|=(52098437/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522556231/10000000000 : ℝ)|^4245 ≤ (35141947275971/100000000000000 : ℝ)^3221
        have hw : |(4522556231/10000000000 : ℝ)|=(4522556231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047131023/5000000000 : ℝ)*x 0 + (2621632663/5000000000 : ℝ)*x 1 + (1353766281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047131023/5000000000 : ℝ)^4245 ≤ (637011822157/5000000000000 : ℝ)^3221 := by
    have hnat : (1047131023 : ℕ)^4245*5000000000000^3221 ≤ 637011822157^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047131023 5000000000 637011822157 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621632663/5000000000 : ℝ)^4245 ≤ (133447192353/312500000000 : ℝ)^3221 := by
    have hnat : (2621632663 : ℕ)^4245*312500000000^3221 ≤ 133447192353^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621632663 5000000000 133447192353 312500000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353766281/2500000000 : ℝ)^4245 ≤ (22278330998761/50000000000000 : ℝ)^3221 := by
    have hnat : (1353766281 : ℕ)^4245*50000000000000^3221 ≤ 22278330998761^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353766281 2500000000 22278330998761 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047131023/5000000000 : ℝ), (2621632663/5000000000 : ℝ), (1353766281/2500000000 : ℝ)] ![(637011822157/5000000000000 : ℝ), (133447192353/312500000000 : ℝ), (22278330998761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047131023/5000000000 : ℝ)|^4245 ≤ (637011822157/5000000000000 : ℝ)^3221
        have hw : |(-1047131023/5000000000 : ℝ)|=(1047131023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621632663/5000000000 : ℝ)|^4245 ≤ (133447192353/312500000000 : ℝ)^3221
        have hw : |(2621632663/5000000000 : ℝ)|=(2621632663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353766281/2500000000 : ℝ)|^4245 ≤ (22278330998761/50000000000000 : ℝ)^3221
        have hw : |(1353766281/2500000000 : ℝ)|=(1353766281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265282357/500000000 : ℝ)*x 0 + (-2010045303/10000000000 : ℝ)*x 1 + (1353766281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265282357/500000000 : ℝ)^4245 ≤ (43373944572571/100000000000000 : ℝ)^3221 := by
    have hnat : (265282357 : ℕ)^4245*100000000000000^3221 ≤ 43373944572571^3221*500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265282357 500000000 43373944572571 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010045303/10000000000 : ℝ)^4245 ≤ (12069393422103/100000000000000 : ℝ)^3221 := by
    have hnat : (2010045303 : ℕ)^4245*100000000000000^3221 ≤ 12069393422103^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010045303 10000000000 12069393422103 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353766281/2500000000 : ℝ)^4245 ≤ (22278330998761/50000000000000 : ℝ)^3221 := by
    have hnat : (1353766281 : ℕ)^4245*50000000000000^3221 ≤ 22278330998761^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353766281 2500000000 22278330998761 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265282357/500000000 : ℝ), (-2010045303/10000000000 : ℝ), (1353766281/2500000000 : ℝ)] ![(43373944572571/100000000000000 : ℝ), (12069393422103/100000000000000 : ℝ), (22278330998761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265282357/500000000 : ℝ)|^4245 ≤ (43373944572571/100000000000000 : ℝ)^3221
        have hw : |(265282357/500000000 : ℝ)|=(265282357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2010045303/10000000000 : ℝ)|^4245 ≤ (12069393422103/100000000000000 : ℝ)^3221
        have hw : |(-2010045303/10000000000 : ℝ)|=(2010045303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353766281/2500000000 : ℝ)|^4245 ≤ (22278330998761/50000000000000 : ℝ)^3221
        have hw : |(1353766281/2500000000 : ℝ)|=(1353766281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265282357/500000000 : ℝ)*x 0 + (1353766281/2500000000 : ℝ)*x 1 + (-2010045303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265282357/500000000 : ℝ)^4245 ≤ (43373944572571/100000000000000 : ℝ)^3221 := by
    have hnat : (265282357 : ℕ)^4245*100000000000000^3221 ≤ 43373944572571^3221*500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265282357 500000000 43373944572571 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353766281/2500000000 : ℝ)^4245 ≤ (22278330998761/50000000000000 : ℝ)^3221 := by
    have hnat : (1353766281 : ℕ)^4245*50000000000000^3221 ≤ 22278330998761^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353766281 2500000000 22278330998761 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010045303/10000000000 : ℝ)^4245 ≤ (12069393422103/100000000000000 : ℝ)^3221 := by
    have hnat : (2010045303 : ℕ)^4245*100000000000000^3221 ≤ 12069393422103^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010045303 10000000000 12069393422103 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265282357/500000000 : ℝ), (1353766281/2500000000 : ℝ), (-2010045303/10000000000 : ℝ)] ![(43373944572571/100000000000000 : ℝ), (22278330998761/50000000000000 : ℝ), (12069393422103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265282357/500000000 : ℝ)|^4245 ≤ (43373944572571/100000000000000 : ℝ)^3221
        have hw : |(265282357/500000000 : ℝ)|=(265282357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353766281/2500000000 : ℝ)|^4245 ≤ (22278330998761/50000000000000 : ℝ)^3221
        have hw : |(1353766281/2500000000 : ℝ)|=(1353766281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010045303/10000000000 : ℝ)|^4245 ≤ (12069393422103/100000000000000 : ℝ)^3221
        have hw : |(-2010045303/10000000000 : ℝ)|=(2010045303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s6_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542721103/1250000000 : ℝ)*x 0 + (4521291431/10000000000 : ℝ)*x 1 + (2084573143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542721103/1250000000 : ℝ)^4245 ≤ (4162804263101/12500000000000 : ℝ)^3221 := by
    have hnat : (542721103 : ℕ)^4245*12500000000000^3221 ≤ 4162804263101^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542721103 1250000000 4162804263101 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521291431/10000000000 : ℝ)^4245 ≤ (35128995439091/100000000000000 : ℝ)^3221 := by
    have hnat : (4521291431 : ℕ)^4245*100000000000000^3221 ≤ 35128995439091^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521291431 10000000000 35128995439091 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084573143/5000000000 : ℝ)^4245 ≤ (7892142608947/25000000000000 : ℝ)^3221 := by
    have hnat : (2084573143 : ℕ)^4245*25000000000000^3221 ≤ 7892142608947^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084573143 5000000000 7892142608947 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542721103/1250000000 : ℝ), (4521291431/10000000000 : ℝ), (2084573143/5000000000 : ℝ)] ![(4162804263101/12500000000000 : ℝ), (35128995439091/100000000000000 : ℝ), (7892142608947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542721103/1250000000 : ℝ)|^4245 ≤ (4162804263101/12500000000000 : ℝ)^3221
        have hw : |(542721103/1250000000 : ℝ)|=(542721103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521291431/10000000000 : ℝ)|^4245 ≤ (35128995439091/100000000000000 : ℝ)^3221
        have hw : |(4521291431/10000000000 : ℝ)|=(4521291431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084573143/5000000000 : ℝ)|^4245 ≤ (7892142608947/25000000000000 : ℝ)^3221
        have hw : |(2084573143/5000000000 : ℝ)|=(2084573143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (344/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1467/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2749/25000 : ℝ) ^ (1061/256 : ℝ) ≤ (10625940553305461/100000000000000000000 : ℝ) := by
    have hpowers : (2749/25000 : ℝ)^1061 ≤ (10625940553305461/100000000000000000000 : ℝ)^256 := by
      have hnat : (2749 : ℕ)^1061*100000000000000000000^256 ≤ 10625940553305461^256*25000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2749 25000 10625940553305461 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2749/25000 : ℝ)) (X := (10625940553305461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7341/50000 : ℝ) ^ (1061/256 : ℝ) ≤ (1760699778376843/5000000000000000000 : ℝ) := by
    have hpowers : (7341/50000 : ℝ)^1061 ≤ (1760699778376843/5000000000000000000 : ℝ)^256 := by
      have hnat : (7341 : ℕ)^1061*5000000000000000000^256 ≤ 1760699778376843^256*50000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7341 50000 1760699778376843 5000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7341/50000 : ℝ)) (X := (1760699778376843/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010625940553305461/50000000000000000000 : ℝ) ≤ (125006409098729/125000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50010625940553305461/50000000000000000000 : ℝ)^256 ≤ (125006409098729/125000000000000 : ℝ)^1061 := by
      have hnat : (50010625940553305461 : ℕ)^256*125000000000000^1061 ≤ 125006409098729^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010625940553305461 50000000000000000000 125006409098729 125000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125006409098729/125000000000000 : ℝ)) (X := (50010625940553305461/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045839936120842321/100000000000000000000 : ℝ) ≤ (500055292099427/500000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (100045839936120842321/100000000000000000000 : ℝ)^256 ≤ (500055292099427/500000000000000 : ℝ)^1061 := by
      have hnat : (100045839936120842321 : ℕ)^256*500000000000000^1061 ≤ 500055292099427^1061*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045839936120842321 100000000000000000000 500055292099427 500000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500055292099427/500000000000000 : ℝ)) (X := (100045839936120842321/100000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501760699778376843/2500000000000000000 : ℝ) ≤ (250042473901969/250000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (2501760699778376843/2500000000000000000 : ℝ)^256 ≤ (250042473901969/250000000000000 : ℝ)^1061 := by
      have hnat : (2501760699778376843 : ℕ)^256*250000000000000^1061 ≤ 250042473901969^1061*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501760699778376843 2500000000000000000 250042473901969 250000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250042473901969/250000000000000 : ℝ)) (X := (2501760699778376843/2500000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10625940553305461/100000000000000000000 : ℝ) ≤ ((28788161054657101/28796875000000000 : ℝ)+2*(29655704511/18430000000000 : ℝ)*(2749/25000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (28788161054657101/28796875000000000 : ℝ)+2*(29655704511/18430000000000 : ℝ)*(2749/25000 : ℝ)=(125006409098729/125000000000000 : ℝ) by norm_num, show 1+2*(10625940553305461/100000000000000000000 : ℝ)=(50010625940553305461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1760699778376843/5000000000000000000 : ℝ)+(10625940553305461/100000000000000000000 : ℝ) ≤ ((28788161054657101/28796875000000000 : ℝ)+(29655704511/18430000000000 : ℝ)*((7341/50000 : ℝ)+(2749/25000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (28788161054657101/28796875000000000 : ℝ)+(29655704511/18430000000000 : ℝ)*((7341/50000 : ℝ)+(2749/25000 : ℝ))=(500055292099427/500000000000000 : ℝ) by norm_num, show 1+(1760699778376843/5000000000000000000 : ℝ)+(10625940553305461/100000000000000000000 : ℝ)=(100045839936120842321/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1760699778376843/5000000000000000000 : ℝ) ≤ ((28788161054657101/28796875000000000 : ℝ)+2*(29655704511/18430000000000 : ℝ)*(7341/50000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (28788161054657101/28796875000000000 : ℝ)+2*(29655704511/18430000000000 : ℝ)*(7341/50000 : ℝ)=(250042473901969/250000000000000 : ℝ) by norm_num, show 1+2*(1760699778376843/5000000000000000000 : ℝ)=(2501760699778376843/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28788161054657101/28796875000000000 : ℝ)*(X 1 0+X 2 0)+(29655704511/18430000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (28788161054657101/28796875000000000 : ℝ)) (alpha := (29655704511/18430000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28788161054657101/28796875000000000 : ℝ)*(X 0 1+X 2 1)+(29655704511/18430000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (28788161054657101/28796875000000000 : ℝ)) (alpha := (29655704511/18430000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28788161054657101/28796875000000000 : ℝ)*(X 0 2+X 1 2)+(29655704511/18430000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (7341/50000 : ℝ)) (c := (28788161054657101/28796875000000000 : ℝ)) (alpha := (29655704511/18430000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-523562299/2500000000 : ℝ)*X 0 0+(5415685341/10000000000 : ℝ)*X 0 1+(5242648293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349909603/10000000000 : ℝ)*X 1 0+(-2182462151/10000000000 : ℝ)*X 1 1+(5242648291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674954811/5000000000 : ℝ)*X 2 0+(524264827/1000000000 : ℝ)*X 2 1+(-1091231077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4341742543/10000000000 : ℝ)*X 0 0+(52098437/125000000 : ℝ)*X 0 1+(4522556231/10000000000 : ℝ)*X 0 2+(4341742543/10000000000 : ℝ)*X 1 0+(52098437/125000000 : ℝ)*X 1 1+(4522556231/10000000000 : ℝ)*X 1 2+(4341742543/10000000000 : ℝ)*X 2 0+(52098437/125000000 : ℝ)*X 2 1+(4522556231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1047131023/5000000000 : ℝ)*X 0 0+(2621632663/5000000000 : ℝ)*X 0 1+(1353766281/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265282357/500000000 : ℝ)*X 1 0+(-2010045303/10000000000 : ℝ)*X 1 1+(1353766281/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265282357/500000000 : ℝ)*X 2 0+(1353766281/2500000000 : ℝ)*X 2 1+(-2010045303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542721103/1250000000 : ℝ)*X 0 0+(4521291431/10000000000 : ℝ)*X 0 1+(2084573143/5000000000 : ℝ)*X 0 2+(542721103/1250000000 : ℝ)*X 1 0+(4521291431/10000000000 : ℝ)*X 1 1+(2084573143/5000000000 : ℝ)*X 1 2+(542721103/1250000000 : ℝ)*X 2 0+(4521291431/10000000000 : ℝ)*X 2 1+(2084573143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7711230463305031653290091/2879687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (499597283/100000000000000 : ℝ)*(base19) + (454582661/100000000000000 : ℝ)*(base23) + (876569/2500000000000 : ℝ)*(lower2) + (77955911/100000000000000 : ℝ)*(upper3) + (1850189/6250000000000 : ℝ)*(upper5) + (1074821417258109/25000000000000 : ℝ)*(major0) + (1074821417258109/25000000000000 : ℝ)*(major1) + (1074821417258109/25000000000000 : ℝ)*(major2) + (5779119209111883/100000000000000 : ℝ)*(sp0) + (5779127906079827/100000000000000 : ℝ)*(sp1) + (115582559021889/2000000000000 : ℝ)*(sp2) + (704859317561089/25000000000000 : ℝ)*(sp3) + (9196565227/100000000000000 : ℝ)*(sp4) + (5572883361/100000000000000 : ℝ)*(sp7) + (704860710781929/25000000000000 : ℝ)*(f.failure) + (577912840567711/10000000000000 : ℝ)*(f.sum) + (50033541363/921500000000000000000000000 : ℝ)*base65 + (6508392405073393/1439843750000000000000000000000 : ℝ)*base67 + (92569279454078303/5759375000000000000000000000000 : ℝ)*base70 + (27477486131178303/5759375000000000000000000000000 : ℝ)*base72 + (1018511364699/184300000000000000000000000 : ℝ)*base74 + (27812691466484553/5759375000000000000000000000000 : ℝ)*base76 + (424993216723393/1439843750000000000000000000000 : ℝ)*base77 + (97681695232784553/5759375000000000000000000000000 : ℝ)*base80 + (159681354917/921500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9515157/1250000000000000000000 : ℝ)*base89 + (9515157/1250000000000000000000 : ℝ)*base91 + (9515157/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11633554076567943822530853/1151875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1797089997/100000000000000 : ℝ)*(base19) + (1952487569/100000000000000 : ℝ)*(base23) + (205269033/100000000000000 : ℝ)*(upper3) + (17617129/25000000000000 : ℝ)*(lower4) + (206915163/100000000000000 : ℝ)*(upper5) + (108255815908781/2500000000000 : ℝ)*(major0) + (108255815908781/2500000000000 : ℝ)*(major1) + (108255815908781/2500000000000 : ℝ)*(major2) + (35883098909/100000000000000 : ℝ)*(sp1) + (38589653979/100000000000000 : ℝ)*(sp2) + (5820727278328943/100000000000000 : ℝ)*(sp4) + (5820689598140037/100000000000000 : ℝ)*(sp5) + (1164137347237479/20000000000000 : ℝ)*(sp6) + (70993441442949/2500000000000 : ℝ)*(sp7) + (70993441442949/2500000000000 : ℝ)*(f.failure) + (5820727278328943/100000000000000 : ℝ)*(f.sum) + (6635614292107/921500000000000000000000000 : ℝ)*base65 + (11846706524960827/575937500000000000000000000000 : ℝ)*base68 + (1004630838371351/287968750000000000000000000000 : ℝ)*base70 + (233192397713529/1151875000000000000000000000000 : ℝ)*base72 + (20780567981/184300000000000000000000000 : ℝ)*base73 + (4525924492563529/1151875000000000000000000000000 : ℝ)*base76 + (2075946476929577/575937500000000000000000000000 : ℝ)*base78 + (3922813201509577/575937500000000000000000000000 : ℝ)*base80 + (3108468696393/1843000000000000000000000000 : ℝ)*base81 + (301183/125000000000000000000 : ℝ)*base90 + (301183/125000000000000000000 : ℝ)*base92 + (301183/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1285_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1467/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1285_s7_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2094260161/10000000000 : ℝ)*x 0 + (541557697/1000000000 : ℝ)*x 1 + (2621374799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094260161/10000000000 : ℝ)^4245 ≤ (12740221330347/100000000000000 : ℝ)^3221 := by
    have hnat : (2094260161 : ℕ)^4245*100000000000000^3221 ≤ 12740221330347^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094260161 10000000000 12740221330347 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541557697/1000000000 : ℝ)^4245 ≤ (11140553155263/25000000000000 : ℝ)^3221 := by
    have hnat : (541557697 : ℕ)^4245*25000000000000^3221 ≤ 11140553155263^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541557697 1000000000 11140553155263 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621374799/5000000000 : ℝ)^4245 ≤ (133429893851/312500000000 : ℝ)^3221 := by
    have hnat : (2621374799 : ℕ)^4245*312500000000^3221 ≤ 133429893851^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621374799 5000000000 133429893851 312500000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2094260161/10000000000 : ℝ), (541557697/1000000000 : ℝ), (2621374799/5000000000 : ℝ)] ![(12740221330347/100000000000000 : ℝ), (11140553155263/25000000000000 : ℝ), (133429893851/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2094260161/10000000000 : ℝ)|^4245 ≤ (12740221330347/100000000000000 : ℝ)^3221
        have hw : |(-2094260161/10000000000 : ℝ)|=(2094260161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541557697/1000000000 : ℝ)|^4245 ≤ (11140553155263/25000000000000 : ℝ)^3221
        have hw : |(541557697/1000000000 : ℝ)|=(541557697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621374799/5000000000 : ℝ)|^4245 ≤ (133429893851/312500000000 : ℝ)^3221
        have hw : |(2621374799/5000000000 : ℝ)|=(2621374799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674941483/5000000000 : ℝ)*x 0 + (-1091181687/5000000000 : ℝ)*x 1 + (2621374929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674941483/5000000000 : ℝ)^4245 ≤ (43851172414049/100000000000000 : ℝ)^3221 := by
    have hnat : (2674941483 : ℕ)^4245*100000000000000^3221 ≤ 43851172414049^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674941483 5000000000 43851172414049 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091181687/5000000000 : ℝ)^4245 ≤ (1345125875741/10000000000000 : ℝ)^3221 := by
    have hnat : (1091181687 : ℕ)^4245*10000000000000^3221 ≤ 1345125875741^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091181687 5000000000 1345125875741 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621374929/5000000000 : ℝ)^4245 ≤ (42697568822963/100000000000000 : ℝ)^3221 := by
    have hnat : (2621374929 : ℕ)^4245*100000000000000^3221 ≤ 42697568822963^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621374929 5000000000 42697568822963 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674941483/5000000000 : ℝ), (-1091181687/5000000000 : ℝ), (2621374929/5000000000 : ℝ)] ![(43851172414049/100000000000000 : ℝ), (1345125875741/10000000000000 : ℝ), (42697568822963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674941483/5000000000 : ℝ)|^4245 ≤ (43851172414049/100000000000000 : ℝ)^3221
        have hw : |(2674941483/5000000000 : ℝ)|=(2674941483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091181687/5000000000 : ℝ)|^4245 ≤ (1345125875741/10000000000000 : ℝ)^3221
        have hw : |(-1091181687/5000000000 : ℝ)|=(1091181687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621374929/5000000000 : ℝ)|^4245 ≤ (42697568822963/100000000000000 : ℝ)^3221
        have hw : |(2621374929/5000000000 : ℝ)|=(2621374929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53498823/100000000 : ℝ)*x 0 + (1048550173/2000000000 : ℝ)*x 1 + (-136397683/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53498823/100000000 : ℝ)^4245 ≤ (43851165219591/100000000000000 : ℝ)^3221 := by
    have hnat : (53498823 : ℕ)^4245*100000000000000^3221 ≤ 43851165219591^3221*100000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53498823 100000000 43851165219591 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048550173/2000000000 : ℝ)^4245 ≤ (42697579631339/100000000000000 : ℝ)^3221 := by
    have hnat : (1048550173 : ℕ)^4245*100000000000000^3221 ≤ 42697579631339^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048550173 2000000000 42697579631339 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136397683/625000000 : ℝ)^4245 ≤ (13451255134499/100000000000000 : ℝ)^3221 := by
    have hnat : (136397683 : ℕ)^4245*100000000000000^3221 ≤ 13451255134499^3221*625000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136397683 625000000 13451255134499 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53498823/100000000 : ℝ), (1048550173/2000000000 : ℝ), (-136397683/625000000 : ℝ)] ![(43851165219591/100000000000000 : ℝ), (42697579631339/100000000000000 : ℝ), (13451255134499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53498823/100000000 : ℝ)|^4245 ≤ (43851165219591/100000000000000 : ℝ)^3221
        have hw : |(53498823/100000000 : ℝ)|=(53498823/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048550173/2000000000 : ℝ)|^4245 ≤ (42697579631339/100000000000000 : ℝ)^3221
        have hw : |(1048550173/2000000000 : ℝ)|=(1048550173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136397683/625000000 : ℝ)|^4245 ≤ (13451255134499/100000000000000 : ℝ)^3221
        have hw : |(-136397683/625000000 : ℝ)|=(136397683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (27135947/62500000 : ℝ)*x 0 + (833617591/2000000000 : ℝ)*x 1 + (4522339831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27135947/62500000 : ℝ)^4245 ≤ (16651129591797/50000000000000 : ℝ)^3221 := by
    have hnat : (27135947 : ℕ)^4245*50000000000000^3221 ≤ 16651129591797^3221*62500000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27135947 62500000 16651129591797 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833617591/2000000000 : ℝ)^4245 ≤ (3155800958897/10000000000000 : ℝ)^3221 := by
    have hnat : (833617591 : ℕ)^4245*10000000000000^3221 ≤ 3155800958897^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833617591 2000000000 3155800958897 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522339831/10000000000 : ℝ)^4245 ≤ (8784932802391/25000000000000 : ℝ)^3221 := by
    have hnat : (4522339831 : ℕ)^4245*25000000000000^3221 ≤ 8784932802391^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522339831 10000000000 8784932802391 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27135947/62500000 : ℝ), (833617591/2000000000 : ℝ), (4522339831/10000000000 : ℝ)] ![(16651129591797/50000000000000 : ℝ), (3155800958897/10000000000000 : ℝ), (8784932802391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27135947/62500000 : ℝ)|^4245 ≤ (16651129591797/50000000000000 : ℝ)^3221
        have hw : |(27135947/62500000 : ℝ)|=(27135947/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833617591/2000000000 : ℝ)|^4245 ≤ (3155800958897/10000000000000 : ℝ)^3221
        have hw : |(833617591/2000000000 : ℝ)|=(833617591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522339831/10000000000 : ℝ)|^4245 ≤ (8784932802391/25000000000000 : ℝ)^3221
        have hw : |(4522339831/10000000000 : ℝ)|=(4522339831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418854537/2000000000 : ℝ)*x 0 + (524336549/1000000000 : ℝ)*x 1 + (2707479057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418854537/2000000000 : ℝ)^4245 ≤ (796270108769/6250000000000 : ℝ)^3221 := by
    have hnat : (418854537 : ℕ)^4245*6250000000000^3221 ≤ 796270108769^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418854537 2000000000 796270108769 6250000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524336549/1000000000 : ℝ)^4245 ≤ (1708167066977/4000000000000 : ℝ)^3221 := by
    have hnat : (524336549 : ℕ)^4245*4000000000000^3221 ≤ 1708167066977^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524336549 1000000000 1708167066977 4000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707479057/5000000000 : ℝ)^4245 ≤ (44555501567561/100000000000000 : ℝ)^3221 := by
    have hnat : (2707479057 : ℕ)^4245*100000000000000^3221 ≤ 44555501567561^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707479057 5000000000 44555501567561 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418854537/2000000000 : ℝ), (524336549/1000000000 : ℝ), (2707479057/5000000000 : ℝ)] ![(796270108769/6250000000000 : ℝ), (1708167066977/4000000000000 : ℝ), (44555501567561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418854537/2000000000 : ℝ)|^4245 ≤ (796270108769/6250000000000 : ℝ)^3221
        have hw : |(-418854537/2000000000 : ℝ)|=(418854537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524336549/1000000000 : ℝ)|^4245 ≤ (1708167066977/4000000000000 : ℝ)^3221
        have hw : |(524336549/1000000000 : ℝ)|=(524336549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707479057/5000000000 : ℝ)|^4245 ≤ (44555501567561/100000000000000 : ℝ)^3221
        have hw : |(2707479057/5000000000 : ℝ)|=(2707479057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061134787/2000000000 : ℝ)*x 0 + (-100507773/500000000 : ℝ)*x 1 + (2707479057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061134787/2000000000 : ℝ)^4245 ≤ (21687116631251/50000000000000 : ℝ)^3221 := by
    have hnat : (1061134787 : ℕ)^4245*50000000000000^3221 ≤ 21687116631251^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061134787 2000000000 21687116631251 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100507773/500000000 : ℝ)^4245 ≤ (482810606121/4000000000000 : ℝ)^3221 := by
    have hnat : (100507773 : ℕ)^4245*4000000000000^3221 ≤ 482810606121^3221*500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100507773 500000000 482810606121 4000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707479057/5000000000 : ℝ)^4245 ≤ (44555501567561/100000000000000 : ℝ)^3221 := by
    have hnat : (2707479057 : ℕ)^4245*100000000000000^3221 ≤ 44555501567561^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707479057 5000000000 44555501567561 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061134787/2000000000 : ℝ), (-100507773/500000000 : ℝ), (2707479057/5000000000 : ℝ)] ![(21687116631251/50000000000000 : ℝ), (482810606121/4000000000000 : ℝ), (44555501567561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061134787/2000000000 : ℝ)|^4245 ≤ (21687116631251/50000000000000 : ℝ)^3221
        have hw : |(1061134787/2000000000 : ℝ)|=(1061134787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100507773/500000000 : ℝ)|^4245 ≤ (482810606121/4000000000000 : ℝ)^3221
        have hw : |(-100507773/500000000 : ℝ)|=(100507773/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707479057/5000000000 : ℝ)|^4245 ≤ (44555501567561/100000000000000 : ℝ)^3221
        have hw : |(2707479057/5000000000 : ℝ)|=(2707479057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305673933/10000000000 : ℝ)*x 0 + (1082991623/2000000000 : ℝ)*x 1 + (-2010155461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305673933/10000000000 : ℝ)^4245 ≤ (21687116620477/50000000000000 : ℝ)^3221 := by
    have hnat : (5305673933 : ℕ)^4245*50000000000000^3221 ≤ 21687116620477^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305673933 10000000000 21687116620477 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082991623/2000000000 : ℝ)^4245 ≤ (8911100315681/20000000000000 : ℝ)^3221 := by
    have hnat : (1082991623 : ℕ)^4245*20000000000000^3221 ≤ 8911100315681^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082991623 2000000000 8911100315681 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010155461/10000000000 : ℝ)^4245 ≤ (6035132580469/50000000000000 : ℝ)^3221 := by
    have hnat : (2010155461 : ℕ)^4245*50000000000000^3221 ≤ 6035132580469^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010155461 10000000000 6035132580469 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305673933/10000000000 : ℝ), (1082991623/2000000000 : ℝ), (-2010155461/10000000000 : ℝ)] ![(21687116620477/50000000000000 : ℝ), (8911100315681/20000000000000 : ℝ), (6035132580469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305673933/10000000000 : ℝ)|^4245 ≤ (21687116620477/50000000000000 : ℝ)^3221
        have hw : |(5305673933/10000000000 : ℝ)|=(5305673933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082991623/2000000000 : ℝ)|^4245 ≤ (8911100315681/20000000000000 : ℝ)^3221
        have hw : |(1082991623/2000000000 : ℝ)|=(1082991623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010155461/10000000000 : ℝ)|^4245 ≤ (6035132580469/50000000000000 : ℝ)^3221
        have hw : |(-2010155461/10000000000 : ℝ)|=(2010155461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s7_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170888103/5000000000 : ℝ)*x 0 + (4521078147/10000000000 : ℝ)*x 1 + (2084678829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170888103/5000000000 : ℝ)^4245 ≤ (16651254363707/50000000000000 : ℝ)^3221 := by
    have hnat : (2170888103 : ℕ)^4245*50000000000000^3221 ≤ 16651254363707^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170888103 5000000000 16651254363707 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521078147/10000000000 : ℝ)^4245 ≤ (17563405738189/50000000000000 : ℝ)^3221 := by
    have hnat : (4521078147 : ℕ)^4245*50000000000000^3221 ≤ 17563405738189^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521078147 10000000000 17563405738189 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084678829/5000000000 : ℝ)^4245 ≤ (31570679771513/100000000000000 : ℝ)^3221 := by
    have hnat : (2084678829 : ℕ)^4245*100000000000000^3221 ≤ 31570679771513^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084678829 5000000000 31570679771513 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170888103/5000000000 : ℝ), (4521078147/10000000000 : ℝ), (2084678829/5000000000 : ℝ)] ![(16651254363707/50000000000000 : ℝ), (17563405738189/50000000000000 : ℝ), (31570679771513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170888103/5000000000 : ℝ)|^4245 ≤ (16651254363707/50000000000000 : ℝ)^3221
        have hw : |(2170888103/5000000000 : ℝ)|=(2170888103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521078147/10000000000 : ℝ)|^4245 ≤ (17563405738189/50000000000000 : ℝ)^3221
        have hw : |(4521078147/10000000000 : ℝ)|=(4521078147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084678829/5000000000 : ℝ)|^4245 ≤ (31570679771513/100000000000000 : ℝ)^3221
        have hw : |(2084678829/5000000000 : ℝ)|=(2084678829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1467/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1101/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14667/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1467/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1467/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1467/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1467/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1467/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1467/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (344/3125 : ℝ) ^ (1061/256 : ℝ) ≤ (2668520923803487/25000000000000000000 : ℝ) := by
    have hpowers : (344/3125 : ℝ)^1061 ≤ (2668520923803487/25000000000000000000 : ℝ)^256 := by
      have hnat : (344 : ℕ)^1061*25000000000000000000^256 ≤ 2668520923803487^256*3125^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        344 3125 2668520923803487 25000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (344/3125 : ℝ)) (X := (2668520923803487/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1467/10000 : ℝ) ^ (1061/256 : ℝ) ≤ (3509486351480439/10000000000000000000 : ℝ) := by
    have hpowers : (1467/10000 : ℝ)^1061 ≤ (3509486351480439/10000000000000000000 : ℝ)^256 := by
      have hnat : (1467 : ℕ)^1061*10000000000000000000^256 ≤ 3509486351480439^256*10000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1467 10000 3509486351480439 10000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1467/10000 : ℝ)) (X := (3509486351480439/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502668520923803487/12500000000000000000 : ℝ) ≤ (10000515050735823/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (12502668520923803487/12500000000000000000 : ℝ)^256 ≤ (10000515050735823/10000000000000000 : ℝ)^1061 := by
      have hnat : (12502668520923803487 : ℕ)^256*10000000000000000^1061 ≤ 10000515050735823^1061*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502668520923803487 12500000000000000000 10000515050735823 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000515050735823/10000000000000000 : ℝ)) (X := (12502668520923803487/12500000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022884473605009169/50000000000000000000 : ℝ) ≤ (10001104129750269/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50022884473605009169/50000000000000000000 : ℝ)^256 ≤ (10001104129750269/10000000000000000 : ℝ)^1061 := by
      have hnat : (50022884473605009169 : ℕ)^256*10000000000000000^1061 ≤ 10001104129750269^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022884473605009169 50000000000000000000 10001104129750269 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001104129750269/10000000000000000 : ℝ)) (X := (50022884473605009169/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003509486351480439/5000000000000000000 : ℝ) ≤ (2000338641752943/2000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (5003509486351480439/5000000000000000000 : ℝ)^256 ≤ (2000338641752943/2000000000000000 : ℝ)^1061 := by
      have hnat : (5003509486351480439 : ℕ)^256*2000000000000000^1061 ≤ 2000338641752943^1061*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003509486351480439 5000000000000000000 2000338641752943 2000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000338641752943/2000000000000000 : ℝ)) (X := (5003509486351480439/5000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2668520923803487/25000000000000000000 : ℝ) ≤ ((3660891695221254069/3662000000000000000 : ℝ)+2*(294539507223/183100000000000 : ℝ)*(344/3125 : ℝ))^(1061/256 : ℝ) := by
    rw [show (3660891695221254069/3662000000000000000 : ℝ)+2*(294539507223/183100000000000 : ℝ)*(344/3125 : ℝ)=(10000515050735823/10000000000000000 : ℝ) by norm_num, show 1+2*(2668520923803487/25000000000000000000 : ℝ)=(12502668520923803487/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3509486351480439/10000000000000000000 : ℝ)+(2668520923803487/25000000000000000000 : ℝ) ≤ ((3660891695221254069/3662000000000000000 : ℝ)+(294539507223/183100000000000 : ℝ)*((1467/10000 : ℝ)+(344/3125 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (3660891695221254069/3662000000000000000 : ℝ)+(294539507223/183100000000000 : ℝ)*((1467/10000 : ℝ)+(344/3125 : ℝ))=(10001104129750269/10000000000000000 : ℝ) by norm_num, show 1+(3509486351480439/10000000000000000000 : ℝ)+(2668520923803487/25000000000000000000 : ℝ)=(50022884473605009169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3509486351480439/10000000000000000000 : ℝ) ≤ ((3660891695221254069/3662000000000000000 : ℝ)+2*(294539507223/183100000000000 : ℝ)*(1467/10000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (3660891695221254069/3662000000000000000 : ℝ)+2*(294539507223/183100000000000 : ℝ)*(1467/10000 : ℝ)=(2000338641752943/2000000000000000 : ℝ) by norm_num, show 1+2*(3509486351480439/10000000000000000000 : ℝ)=(5003509486351480439/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3660891695221254069/3662000000000000000 : ℝ)*(X 1 0+X 2 0)+(294539507223/183100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (1467/10000 : ℝ)) (c := (3660891695221254069/3662000000000000000 : ℝ)) (alpha := (294539507223/183100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3660891695221254069/3662000000000000000 : ℝ)*(X 0 1+X 2 1)+(294539507223/183100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (1467/10000 : ℝ)) (c := (3660891695221254069/3662000000000000000 : ℝ)) (alpha := (294539507223/183100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3660891695221254069/3662000000000000000 : ℝ)*(X 0 2+X 1 2)+(294539507223/183100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (1467/10000 : ℝ)) (c := (3660891695221254069/3662000000000000000 : ℝ)) (alpha := (294539507223/183100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2094260161/10000000000 : ℝ)*X 0 0+(541557697/1000000000 : ℝ)*X 0 1+(2621374799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674941483/5000000000 : ℝ)*X 1 0+(-1091181687/5000000000 : ℝ)*X 1 1+(2621374929/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53498823/100000000 : ℝ)*X 2 0+(1048550173/2000000000 : ℝ)*X 2 1+(-136397683/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((27135947/62500000 : ℝ)*X 0 0+(833617591/2000000000 : ℝ)*X 0 1+(4522339831/10000000000 : ℝ)*X 0 2+(27135947/62500000 : ℝ)*X 1 0+(833617591/2000000000 : ℝ)*X 1 1+(4522339831/10000000000 : ℝ)*X 1 2+(27135947/62500000 : ℝ)*X 2 0+(833617591/2000000000 : ℝ)*X 2 1+(4522339831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418854537/2000000000 : ℝ)*X 0 0+(524336549/1000000000 : ℝ)*X 0 1+(2707479057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061134787/2000000000 : ℝ)*X 1 0+(-100507773/500000000 : ℝ)*X 1 1+(2707479057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305673933/10000000000 : ℝ)*X 2 0+(1082991623/2000000000 : ℝ)*X 2 1+(-2010155461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170888103/5000000000 : ℝ)*X 0 0+(4521078147/10000000000 : ℝ)*X 0 1+(2084678829/5000000000 : ℝ)*X 0 2+(2170888103/5000000000 : ℝ)*X 1 0+(4521078147/10000000000 : ℝ)*X 1 1+(2084678829/5000000000 : ℝ)*X 1 2+(2170888103/5000000000 : ℝ)*X 2 0+(4521078147/10000000000 : ℝ)*X 2 1+(2084678829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37124674501249986904090269/45775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (88561867/4000000000000 : ℝ)*(base19) + (962380233/100000000000000 : ℝ)*(base23) + (284264577/100000000000000 : ℝ)*(lower2) + (159186453/50000000000000 : ℝ)*(upper3) + (322382777/100000000000000 : ℝ)*(upper5) + (4304562770913067/100000000000000 : ℝ)*(major0) + (4304562770913067/100000000000000 : ℝ)*(major1) + (1076140692728267/25000000000000 : ℝ)*(major2) + (5786170572183433/100000000000000 : ℝ)*(sp0) + (5786219769430001/100000000000000 : ℝ)*(sp1) + (5786221021096443/100000000000000 : ℝ)*(sp2) + (705719267591013/25000000000000 : ℝ)*(sp3) + (51411293243/100000000000000 : ℝ)*(sp4) + (413452363/1562500000000 : ℝ)*(sp7) + (705725882828821/25000000000000 : ℝ)*(f.failure) + (1446555495869169/25000000000000 : ℝ)*(f.sum) + (10719815335053/3662000000000000000000000000 : ℝ)*base65 + (1862560648249499623/366200000000000000000000000000000 : ℝ)*base67 + (209339076091426577/91550000000000000000000000000000 : ℝ)*base70 + (2541068842094699623/366200000000000000000000000000000 : ℝ)*base71 + (16935427812441/3662000000000000000000000000 : ℝ)*base73 + (184113043215526577/91550000000000000000000000000000 : ℝ)*base76 + (71944739080560377/366200000000000000000000000000000 : ℝ)*base78 + (2098272240207960377/366200000000000000000000000000000 : ℝ)*base80 + (36753065131479/9155000000000000000000000000 : ℝ)*base82 + (9764593/1250000000000000000000 : ℝ)*base89 + (9764593/1250000000000000000000 : ℝ)*base91 + (2735407/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68571959252005510220038641/22887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (269042809/50000000000000 : ℝ)*(base19) + (23306197/4000000000000 : ℝ)*(base23) + (5812139/3125000000000 : ℝ)*(lower1) + (3036303/5000000000000 : ℝ)*(upper3) + (10738153/50000000000000 : ℝ)*(lower4) + (61942911/100000000000000 : ℝ)*(upper5) + (1083863310930363/25000000000000 : ℝ)*(major0) + (1083863310930363/25000000000000 : ℝ)*(major1) + (1083863310930363/25000000000000 : ℝ)*(major2) + (754668307/100000000000000 : ℝ)*(sp2) + (1456936272598013/25000000000000 : ℝ)*(sp4) + (2913872276153217/50000000000000 : ℝ)*(sp5) + (291387187653441/5000000000000 : ℝ)*(sp6) + (710790324295677/25000000000000 : ℝ)*(sp7) + (710790324295677/25000000000000 : ℝ)*(f.failure) + (1456936272598013/25000000000000 : ℝ)*(f.sum) + (3963008041307/1144375000000000000000000000 : ℝ)*base65 + (558531729523422953/91550000000000000000000000000000 : ℝ)*base68 + (580423187129222953/91550000000000000000000000000000 : ℝ)*base70 + (1164267515169477047/91550000000000000000000000000000 : ℝ)*base71 + (525810000473/1144375000000000000000000000 : ℝ)*base74 + (2117016289548622953/91550000000000000000000000000000 : ℝ)*base76 + (118598591054022953/91550000000000000000000000000000 : ℝ)*base78 + (1135088396054672953/91550000000000000000000000000000 : ℝ)*base80 + (8940372496393/1144375000000000000000000000 : ℝ)*base82 + (1106841/1250000000000000000000 : ℝ)*base89 + (1106841/1250000000000000000000 : ℝ)*base91 + (1106841/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1285_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1467/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1285_box_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922325957/10000000000 : ℝ)*x 0 + (5392299407/10000000000 : ℝ)*x 1 + (5392299609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922325957/10000000000 : ℝ)^4245 ≤ (5690046847469/50000000000000 : ℝ)^3221 := by
    have hnat : (1922325957 : ℕ)^4245*50000000000000^3221 ≤ 5690046847469^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922325957 10000000000 5690046847469 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392299407/10000000000 : ℝ)^4245 ≤ (44309952049359/100000000000000 : ℝ)^3221 := by
    have hnat : (5392299407 : ℕ)^4245*100000000000000^3221 ≤ 44309952049359^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392299407 10000000000 44309952049359 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392299609/10000000000 : ℝ)^4245 ≤ (11077488559237/25000000000000 : ℝ)^3221 := by
    have hnat : (5392299609 : ℕ)^4245*25000000000000^3221 ≤ 11077488559237^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392299609 10000000000 11077488559237 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922325957/10000000000 : ℝ), (5392299407/10000000000 : ℝ), (5392299609/10000000000 : ℝ)] ![(5690046847469/50000000000000 : ℝ), (44309952049359/100000000000000 : ℝ), (11077488559237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922325957/10000000000 : ℝ)|^4245 ≤ (5690046847469/50000000000000 : ℝ)^3221
        have hw : |(-1922325957/10000000000 : ℝ)|=(1922325957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392299407/10000000000 : ℝ)|^4245 ≤ (44309952049359/100000000000000 : ℝ)^3221
        have hw : |(5392299407/10000000000 : ℝ)|=(5392299407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392299609/10000000000 : ℝ)|^4245 ≤ (11077488559237/25000000000000 : ℝ)^3221
        have hw : |(5392299609/10000000000 : ℝ)|=(5392299609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330264979/625000000 : ℝ)*x 0 + (-258758147/1250000000 : ℝ)*x 1 + (674037449/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330264979/625000000 : ℝ)^4245 ≤ (5392931024339/12500000000000 : ℝ)^3221 := by
    have hnat : (330264979 : ℕ)^4245*12500000000000^3221 ≤ 5392931024339^3221*625000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330264979 625000000 5392931024339 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258758147/1250000000 : ℝ)^4245 ≤ (784162358563/6250000000000 : ℝ)^3221 := by
    have hnat : (258758147 : ℕ)^4245*6250000000000^3221 ≤ 784162358563^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258758147 1250000000 784162358563 6250000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674037449/1250000000 : ℝ)^4245 ≤ (11077488513211/25000000000000 : ℝ)^3221 := by
    have hnat : (674037449 : ℕ)^4245*25000000000000^3221 ≤ 11077488513211^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674037449 1250000000 11077488513211 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330264979/625000000 : ℝ), (-258758147/1250000000 : ℝ), (674037449/1250000000 : ℝ)] ![(5392931024339/12500000000000 : ℝ), (784162358563/6250000000000 : ℝ), (11077488513211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330264979/625000000 : ℝ)|^4245 ≤ (5392931024339/12500000000000 : ℝ)^3221
        have hw : |(330264979/625000000 : ℝ)|=(330264979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258758147/1250000000 : ℝ)|^4245 ≤ (784162358563/6250000000000 : ℝ)^3221
        have hw : |(-258758147/1250000000 : ℝ)|=(258758147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674037449/1250000000 : ℝ)|^4245 ≤ (11077488513211/25000000000000 : ℝ)^3221
        have hw : |(674037449/1250000000 : ℝ)|=(674037449/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642119843/5000000000 : ℝ)*x 0 + (674037429/1250000000 : ℝ)*x 1 + (-2070065363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642119843/5000000000 : ℝ)^4245 ≤ (10785862107859/25000000000000 : ℝ)^3221 := by
    have hnat : (2642119843 : ℕ)^4245*25000000000000^3221 ≤ 10785862107859^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642119843 5000000000 10785862107859 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674037429/1250000000 : ℝ)^4245 ≤ (443099523201/1000000000000 : ℝ)^3221 := by
    have hnat : (674037429 : ℕ)^4245*1000000000000^3221 ≤ 443099523201^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674037429 1250000000 443099523201 1000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070065363/10000000000 : ℝ)^4245 ≤ (3136649807683/25000000000000 : ℝ)^3221 := by
    have hnat : (2070065363 : ℕ)^4245*25000000000000^3221 ≤ 3136649807683^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070065363 10000000000 3136649807683 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642119843/5000000000 : ℝ), (674037429/1250000000 : ℝ), (-2070065363/10000000000 : ℝ)] ![(10785862107859/25000000000000 : ℝ), (443099523201/1000000000000 : ℝ), (3136649807683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642119843/5000000000 : ℝ)|^4245 ≤ (10785862107859/25000000000000 : ℝ)^3221
        have hw : |(2642119843/5000000000 : ℝ)|=(2642119843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674037429/1250000000 : ℝ)|^4245 ≤ (443099523201/1000000000000 : ℝ)^3221
        have hw : |(674037429/1250000000 : ℝ)|=(674037429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070065363/10000000000 : ℝ)|^4245 ≤ (3136649807683/25000000000000 : ℝ)^3221
        have hw : |(-2070065363/10000000000 : ℝ)|=(2070065363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4491357723/10000000000 : ℝ)*x 0 + (2135484413/5000000000 : ℝ)*x 1 + (427096867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4491357723/10000000000 : ℝ)^4245 ≤ (3482280421581/10000000000000 : ℝ)^3221 := by
    have hnat : (4491357723 : ℕ)^4245*10000000000000^3221 ≤ 3482280421581^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491357723 10000000000 3482280421581 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135484413/5000000000 : ℝ)^4245 ≤ (16294299334837/50000000000000 : ℝ)^3221 := by
    have hnat : (2135484413 : ℕ)^4245*50000000000000^3221 ≤ 16294299334837^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135484413 5000000000 16294299334837 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427096867/1000000000 : ℝ)^4245 ≤ (6517719420187/20000000000000 : ℝ)^3221 := by
    have hnat : (427096867 : ℕ)^4245*20000000000000^3221 ≤ 6517719420187^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427096867 1000000000 6517719420187 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4491357723/10000000000 : ℝ), (2135484413/5000000000 : ℝ), (427096867/1000000000 : ℝ)] ![(3482280421581/10000000000000 : ℝ), (16294299334837/50000000000000 : ℝ), (6517719420187/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4491357723/10000000000 : ℝ)|^4245 ≤ (3482280421581/10000000000000 : ℝ)^3221
        have hw : |(4491357723/10000000000 : ℝ)|=(4491357723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2135484413/5000000000 : ℝ)|^4245 ≤ (16294299334837/50000000000000 : ℝ)^3221
        have hw : |(2135484413/5000000000 : ℝ)|=(2135484413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427096867/1000000000 : ℝ)|^4245 ≤ (6517719420187/20000000000000 : ℝ)^3221
        have hw : |(427096867/1000000000 : ℝ)|=(427096867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1134481393/5000000000 : ℝ)*x 0 + (5263502149/10000000000 : ℝ)*x 1 + (5263501183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134481393/5000000000 : ℝ)^4245 ≤ (14159113893761/100000000000000 : ℝ)^3221 := by
    have hnat : (1134481393 : ℕ)^4245*100000000000000^3221 ≤ 14159113893761^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134481393 5000000000 14159113893761 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263502149/10000000000 : ℝ)^4245 ≤ (10730112058791/25000000000000 : ℝ)^3221 := by
    have hnat : (5263502149 : ℕ)^4245*25000000000000^3221 ≤ 10730112058791^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263502149 10000000000 10730112058791 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263501183/10000000000 : ℝ)^4245 ≤ (42920437853821/100000000000000 : ℝ)^3221 := by
    have hnat : (5263501183 : ℕ)^4245*100000000000000^3221 ≤ 42920437853821^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263501183 10000000000 42920437853821 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1134481393/5000000000 : ℝ), (5263502149/10000000000 : ℝ), (5263501183/10000000000 : ℝ)] ![(14159113893761/100000000000000 : ℝ), (10730112058791/25000000000000 : ℝ), (42920437853821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1134481393/5000000000 : ℝ)|^4245 ≤ (14159113893761/100000000000000 : ℝ)^3221
        have hw : |(-1134481393/5000000000 : ℝ)|=(1134481393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263502149/10000000000 : ℝ)|^4245 ≤ (10730112058791/25000000000000 : ℝ)^3221
        have hw : |(5263502149/10000000000 : ℝ)|=(5263502149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263501183/10000000000 : ℝ)|^4245 ≤ (42920437853821/100000000000000 : ℝ)^3221
        have hw : |(5263501183/10000000000 : ℝ)|=(5263501183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343731271/2500000000 : ℝ)*x 0 + (-2121325193/10000000000 : ℝ)*x 1 + (5263502537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343731271/2500000000 : ℝ)^4245 ≤ (44121890724983/100000000000000 : ℝ)^3221 := by
    have hnat : (1343731271 : ℕ)^4245*100000000000000^3221 ≤ 44121890724983^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343731271 2500000000 44121890724983 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121325193/10000000000 : ℝ)^4245 ≤ (6478828426487/50000000000000 : ℝ)^3221 := by
    have hnat : (2121325193 : ℕ)^4245*50000000000000^3221 ≤ 6478828426487^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121325193 10000000000 6478828426487 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263502537/10000000000 : ℝ)^4245 ≤ (1341264137653/3125000000000 : ℝ)^3221 := by
    have hnat : (5263502537 : ℕ)^4245*3125000000000^3221 ≤ 1341264137653^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263502537 10000000000 1341264137653 3125000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343731271/2500000000 : ℝ), (-2121325193/10000000000 : ℝ), (5263502537/10000000000 : ℝ)] ![(44121890724983/100000000000000 : ℝ), (6478828426487/50000000000000 : ℝ), (1341264137653/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343731271/2500000000 : ℝ)|^4245 ≤ (44121890724983/100000000000000 : ℝ)^3221
        have hw : |(1343731271/2500000000 : ℝ)|=(1343731271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2121325193/10000000000 : ℝ)|^4245 ≤ (6478828426487/50000000000000 : ℝ)^3221
        have hw : |(-2121325193/10000000000 : ℝ)|=(2121325193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263502537/10000000000 : ℝ)|^4245 ≤ (1341264137653/3125000000000 : ℝ)^3221
        have hw : |(5263502537/10000000000 : ℝ)|=(5263502537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671865657/1250000000 : ℝ)*x 0 + (526350243/1000000000 : ℝ)*x 1 + (-424265021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671865657/1250000000 : ℝ)^4245 ≤ (11030473146443/25000000000000 : ℝ)^3221 := by
    have hnat : (671865657 : ℕ)^4245*25000000000000^3221 ≤ 11030473146443^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671865657 1250000000 11030473146443 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526350243/1000000000 : ℝ)^4245 ≤ (8584090250999/20000000000000 : ℝ)^3221 := by
    have hnat : (526350243 : ℕ)^4245*20000000000000^3221 ≤ 8584090250999^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526350243 1000000000 8584090250999 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424265021/2000000000 : ℝ)^4245 ≤ (12957656144557/100000000000000 : ℝ)^3221 := by
    have hnat : (424265021 : ℕ)^4245*100000000000000^3221 ≤ 12957656144557^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424265021 2000000000 12957656144557 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671865657/1250000000 : ℝ), (526350243/1000000000 : ℝ), (-424265021/2000000000 : ℝ)] ![(11030473146443/25000000000000 : ℝ), (8584090250999/20000000000000 : ℝ), (12957656144557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671865657/1250000000 : ℝ)|^4245 ≤ (11030473146443/25000000000000 : ℝ)^3221
        have hw : |(671865657/1250000000 : ℝ)|=(671865657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526350243/1000000000 : ℝ)|^4245 ≤ (8584090250999/20000000000000 : ℝ)^3221
        have hw : |(526350243/1000000000 : ℝ)|=(526350243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424265021/2000000000 : ℝ)|^4245 ≤ (12957656144557/100000000000000 : ℝ)^3221
        have hw : |(-424265021/2000000000 : ℝ)|=(424265021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4191302881/10000000000 : ℝ)*x 0 + (884188089/2000000000 : ℝ)*x 1 + (552617579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191302881/10000000000 : ℝ)^4245 ≤ (31789861588029/100000000000000 : ℝ)^3221 := by
    have hnat : (4191302881 : ℕ)^4245*100000000000000^3221 ≤ 31789861588029^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191302881 10000000000 31789861588029 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884188089/2000000000 : ℝ)^4245 ≤ (8526267062459/25000000000000 : ℝ)^3221 := by
    have hnat : (884188089 : ℕ)^4245*25000000000000^3221 ≤ 8526267062459^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884188089 2000000000 8526267062459 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552617579/1250000000 : ℝ)^4245 ≤ (17052535075529/50000000000000 : ℝ)^3221 := by
    have hnat : (552617579 : ℕ)^4245*50000000000000^3221 ≤ 17052535075529^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552617579 1250000000 17052535075529 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191302881/10000000000 : ℝ), (884188089/2000000000 : ℝ), (552617579/1250000000 : ℝ)] ![(31789861588029/100000000000000 : ℝ), (8526267062459/25000000000000 : ℝ), (17052535075529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191302881/10000000000 : ℝ)|^4245 ≤ (31789861588029/100000000000000 : ℝ)^3221
        have hw : |(4191302881/10000000000 : ℝ)|=(4191302881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884188089/2000000000 : ℝ)|^4245 ≤ (8526267062459/25000000000000 : ℝ)^3221
        have hw : |(884188089/2000000000 : ℝ)|=(884188089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552617579/1250000000 : ℝ)|^4245 ≤ (17052535075529/50000000000000 : ℝ)^3221
        have hw : |(552617579/1250000000 : ℝ)|=(552617579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_8 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1098166191/5000000000 : ℝ)*x 0 + (5175112071/10000000000 : ℝ)*x 1 + (1351584891/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098166191/5000000000 : ℝ)^4245 ≤ (6782422980913/50000000000000 : ℝ)^3221 := by
    have hnat : (1098166191 : ℕ)^4245*50000000000000^3221 ≤ 6782422980913^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098166191 5000000000 6782422980913 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175112071/10000000000 : ℝ)^4245 ≤ (8394617831521/20000000000000 : ℝ)^3221 := by
    have hnat : (5175112071 : ℕ)^4245*20000000000000^3221 ≤ 8394617831521^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175112071 10000000000 8394617831521 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351584891/2500000000 : ℝ)^4245 ≤ (22231032434927/50000000000000 : ℝ)^3221 := by
    have hnat : (1351584891 : ℕ)^4245*50000000000000^3221 ≤ 22231032434927^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351584891 2500000000 22231032434927 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1098166191/5000000000 : ℝ), (5175112071/10000000000 : ℝ), (1351584891/2500000000 : ℝ)] ![(6782422980913/50000000000000 : ℝ), (8394617831521/20000000000000 : ℝ), (22231032434927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1098166191/5000000000 : ℝ)|^4245 ≤ (6782422980913/50000000000000 : ℝ)^3221
        have hw : |(-1098166191/5000000000 : ℝ)|=(1098166191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175112071/10000000000 : ℝ)|^4245 ≤ (8394617831521/20000000000000 : ℝ)^3221
        have hw : |(5175112071/10000000000 : ℝ)|=(5175112071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351584891/2500000000 : ℝ)|^4245 ≤ (22231032434927/50000000000000 : ℝ)^3221
        have hw : |(1351584891/2500000000 : ℝ)|=(1351584891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_9 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274348161/10000000000 : ℝ)*x 0 + (-2064340551/10000000000 : ℝ)*x 1 + (2703169737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274348161/10000000000 : ℝ)^4245 ≤ (10759261394741/25000000000000 : ℝ)^3221 := by
    have hnat : (5274348161 : ℕ)^4245*25000000000000^3221 ≤ 10759261394741^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274348161 10000000000 10759261394741 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064340551/10000000000 : ℝ)^4245 ≤ (6250445253847/50000000000000 : ℝ)^3221 := by
    have hnat : (2064340551 : ℕ)^4245*50000000000000^3221 ≤ 6250445253847^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064340551 10000000000 6250445253847 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703169737/5000000000 : ℝ)^4245 ≤ (2223103194719/5000000000000 : ℝ)^3221 := by
    have hnat : (2703169737 : ℕ)^4245*5000000000000^3221 ≤ 2223103194719^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703169737 5000000000 2223103194719 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274348161/10000000000 : ℝ), (-2064340551/10000000000 : ℝ), (2703169737/5000000000 : ℝ)] ![(10759261394741/25000000000000 : ℝ), (6250445253847/50000000000000 : ℝ), (2223103194719/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274348161/10000000000 : ℝ)|^4245 ≤ (10759261394741/25000000000000 : ℝ)^3221
        have hw : |(5274348161/10000000000 : ℝ)|=(5274348161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064340551/10000000000 : ℝ)|^4245 ≤ (6250445253847/50000000000000 : ℝ)^3221
        have hw : |(-2064340551/10000000000 : ℝ)|=(2064340551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703169737/5000000000 : ℝ)|^4245 ≤ (2223103194719/5000000000000 : ℝ)^3221
        have hw : |(2703169737/5000000000 : ℝ)|=(2703169737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_10 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274347827/10000000000 : ℝ)*x 0 + (2703169639/5000000000 : ℝ)*x 1 + (-2064341267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274347827/10000000000 : ℝ)^4245 ≤ (21518520993603/50000000000000 : ℝ)^3221 := by
    have hnat : (5274347827 : ℕ)^4245*50000000000000^3221 ≤ 21518520993603^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274347827 10000000000 21518520993603 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703169639/5000000000 : ℝ)^4245 ≤ (22231030885007/50000000000000 : ℝ)^3221 := by
    have hnat : (2703169639 : ℕ)^4245*50000000000000^3221 ≤ 22231030885007^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703169639 5000000000 22231030885007 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064341267/10000000000 : ℝ)^4245 ≤ (12500896221949/100000000000000 : ℝ)^3221 := by
    have hnat : (2064341267 : ℕ)^4245*100000000000000^3221 ≤ 12500896221949^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064341267 10000000000 12500896221949 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274347827/10000000000 : ℝ), (2703169639/5000000000 : ℝ), (-2064341267/10000000000 : ℝ)] ![(21518520993603/50000000000000 : ℝ), (22231030885007/50000000000000 : ℝ), (12500896221949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274347827/10000000000 : ℝ)|^4245 ≤ (21518520993603/50000000000000 : ℝ)^3221
        have hw : |(5274347827/10000000000 : ℝ)|=(5274347827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703169639/5000000000 : ℝ)|^4245 ≤ (22231030885007/50000000000000 : ℝ)^3221
        have hw : |(2703169639/5000000000 : ℝ)|=(2703169639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064341267/10000000000 : ℝ)|^4245 ≤ (12500896221949/100000000000000 : ℝ)^3221
        have hw : |(-2064341267/10000000000 : ℝ)|=(2064341267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_11 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4523505479/10000000000 : ℝ)*x 0 + (2127303821/5000000000 : ℝ)*x 1 + (425460669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4523505479/10000000000 : ℝ)^4245 ≤ (35151668545777/100000000000000 : ℝ)^3221 := by
    have hnat : (4523505479 : ℕ)^4245*100000000000000^3221 ≤ 35151668545777^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523505479 10000000000 35151668545777 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127303821/5000000000 : ℝ)^4245 ≤ (32424170502253/100000000000000 : ℝ)^3221 := by
    have hnat : (2127303821 : ℕ)^4245*100000000000000^3221 ≤ 32424170502253^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127303821 5000000000 32424170502253 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425460669/1000000000 : ℝ)^4245 ≤ (16212080470297/50000000000000 : ℝ)^3221 := by
    have hnat : (425460669 : ℕ)^4245*50000000000000^3221 ≤ 16212080470297^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425460669 1000000000 16212080470297 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4523505479/10000000000 : ℝ), (2127303821/5000000000 : ℝ), (425460669/1000000000 : ℝ)] ![(35151668545777/100000000000000 : ℝ), (32424170502253/100000000000000 : ℝ), (16212080470297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4523505479/10000000000 : ℝ)|^4245 ≤ (35151668545777/100000000000000 : ℝ)^3221
        have hw : |(4523505479/10000000000 : ℝ)|=(4523505479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2127303821/5000000000 : ℝ)|^4245 ≤ (32424170502253/100000000000000 : ℝ)^3221
        have hw : |(2127303821/5000000000 : ℝ)|=(2127303821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425460669/1000000000 : ℝ)|^4245 ≤ (16212080470297/50000000000000 : ℝ)^3221
        have hw : |(425460669/1000000000 : ℝ)|=(425460669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_12 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-997705211/5000000000 : ℝ)*x 0 + (2739173991/5000000000 : ℝ)*x 1 + (2626243091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (997705211/5000000000 : ℝ)^4245 ≤ (11953715092557/100000000000000 : ℝ)^3221 := by
    have hnat : (997705211 : ℕ)^4245*100000000000000^3221 ≤ 11953715092557^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997705211 5000000000 11953715092557 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739173991/5000000000 : ℝ)^4245 ≤ (45244182895527/100000000000000 : ℝ)^3221 := by
    have hnat : (2739173991 : ℕ)^4245*100000000000000^3221 ≤ 45244182895527^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739173991 5000000000 45244182895527 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626243091/5000000000 : ℝ)^4245 ≤ (4280210199469/10000000000000 : ℝ)^3221 := by
    have hnat : (2626243091 : ℕ)^4245*10000000000000^3221 ≤ 4280210199469^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626243091 5000000000 4280210199469 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-997705211/5000000000 : ℝ), (2739173991/5000000000 : ℝ), (2626243091/5000000000 : ℝ)] ![(11953715092557/100000000000000 : ℝ), (45244182895527/100000000000000 : ℝ), (4280210199469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-997705211/5000000000 : ℝ)|^4245 ≤ (11953715092557/100000000000000 : ℝ)^3221
        have hw : |(-997705211/5000000000 : ℝ)|=(997705211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739173991/5000000000 : ℝ)|^4245 ≤ (45244182895527/100000000000000 : ℝ)^3221
        have hw : |(2739173991/5000000000 : ℝ)|=(2739173991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626243091/5000000000 : ℝ)|^4245 ≤ (4280210199469/10000000000000 : ℝ)^3221
        have hw : |(2626243091/5000000000 : ℝ)|=(2626243091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_13 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215307159/400000000 : ℝ)*x 0 + (-1062801473/5000000000 : ℝ)*x 1 + (2626242981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215307159/400000000 : ℝ)^4245 ≤ (22102897868651/50000000000000 : ℝ)^3221 := by
    have hnat : (215307159 : ℕ)^4245*50000000000000^3221 ≤ 22102897868651^3221*400000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215307159 400000000 22102897868651 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062801473/5000000000 : ℝ)^4245 ≤ (12992104615909/100000000000000 : ℝ)^3221 := by
    have hnat : (1062801473 : ℕ)^4245*100000000000000^3221 ≤ 12992104615909^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062801473 5000000000 12992104615909 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626242981/5000000000 : ℝ)^4245 ≤ (42802099631983/100000000000000 : ℝ)^3221 := by
    have hnat : (2626242981 : ℕ)^4245*100000000000000^3221 ≤ 42802099631983^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626242981 5000000000 42802099631983 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215307159/400000000 : ℝ), (-1062801473/5000000000 : ℝ), (2626242981/5000000000 : ℝ)] ![(22102897868651/50000000000000 : ℝ), (12992104615909/100000000000000 : ℝ), (42802099631983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215307159/400000000 : ℝ)|^4245 ≤ (22102897868651/50000000000000 : ℝ)^3221
        have hw : |(215307159/400000000 : ℝ)|=(215307159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062801473/5000000000 : ℝ)|^4245 ≤ (12992104615909/100000000000000 : ℝ)^3221
        have hw : |(-1062801473/5000000000 : ℝ)|=(1062801473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626242981/5000000000 : ℝ)|^4245 ≤ (42802099631983/100000000000000 : ℝ)^3221
        have hw : |(2626242981/5000000000 : ℝ)|=(2626242981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_14 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336417433/625000000 : ℝ)*x 0 + (2626243079/5000000000 : ℝ)*x 1 + (-2125602747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336417433/625000000 : ℝ)^4245 ≤ (22102897614299/50000000000000 : ℝ)^3221 := by
    have hnat : (336417433 : ℕ)^4245*50000000000000^3221 ≤ 22102897614299^3221*625000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336417433 625000000 22102897614299 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626243079/5000000000 : ℝ)^4245 ≤ (2140105086847/5000000000000 : ℝ)^3221 := by
    have hnat : (2626243079 : ℕ)^4245*5000000000000^3221 ≤ 2140105086847^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626243079 5000000000 2140105086847 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125602747/10000000000 : ℝ)^4245 ≤ (6496051506447/50000000000000 : ℝ)^3221 := by
    have hnat : (2125602747 : ℕ)^4245*50000000000000^3221 ≤ 6496051506447^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125602747 10000000000 6496051506447 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336417433/625000000 : ℝ), (2626243079/5000000000 : ℝ), (-2125602747/10000000000 : ℝ)] ![(22102897614299/50000000000000 : ℝ), (2140105086847/5000000000000 : ℝ), (6496051506447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336417433/625000000 : ℝ)|^4245 ≤ (22102897614299/50000000000000 : ℝ)^3221
        have hw : |(336417433/625000000 : ℝ)|=(336417433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626243079/5000000000 : ℝ)|^4245 ≤ (2140105086847/5000000000000 : ℝ)^3221
        have hw : |(2626243079/5000000000 : ℝ)|=(2626243079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125602747/10000000000 : ℝ)|^4245 ≤ (6496051506447/50000000000000 : ℝ)^3221
        have hw : |(-2125602747/10000000000 : ℝ)|=(2125602747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_box_15 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260324651/625000000 : ℝ)*x 0 + (4433756937/10000000000 : ℝ)*x 1 + (2216878169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260324651/625000000 : ℝ)^4245 ≤ (1970571247907/6250000000000 : ℝ)^3221 := by
    have hnat : (260324651 : ℕ)^4245*6250000000000^3221 ≤ 1970571247907^3221*625000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260324651 625000000 1970571247907 6250000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433756937/10000000000 : ℝ)^4245 ≤ (17117716526597/50000000000000 : ℝ)^3221 := by
    have hnat : (4433756937 : ℕ)^4245*50000000000000^3221 ≤ 17117716526597^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433756937 10000000000 17117716526597 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216878169/5000000000 : ℝ)^4245 ≤ (4279428369697/12500000000000 : ℝ)^3221 := by
    have hnat : (2216878169 : ℕ)^4245*12500000000000^3221 ≤ 4279428369697^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216878169 5000000000 4279428369697 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260324651/625000000 : ℝ), (4433756937/10000000000 : ℝ), (2216878169/5000000000 : ℝ)] ![(1970571247907/6250000000000 : ℝ), (17117716526597/50000000000000 : ℝ), (4279428369697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260324651/625000000 : ℝ)|^4245 ≤ (1970571247907/6250000000000 : ℝ)^3221
        have hw : |(260324651/625000000 : ℝ)|=(260324651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433756937/10000000000 : ℝ)|^4245 ≤ (17117716526597/50000000000000 : ℝ)^3221
        have hw : |(4433756937/10000000000 : ℝ)|=(4433756937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216878169/5000000000 : ℝ)|^4245 ≤ (4279428369697/12500000000000 : ℝ)^3221
        have hw : |(2216878169/5000000000 : ℝ)|=(2216878169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31419/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3677/6250 : ℝ) ∧ (39807/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84127/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1101/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14667/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1101/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1101/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14667/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1101/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1101/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14667/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1101/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1101/10000 : ℝ) ^ (1061/256 : ℝ) ≤ (133526545173547/1250000000000000000 : ℝ) := by
    have hpowers : (1101/10000 : ℝ)^1061 ≤ (133526545173547/1250000000000000000 : ℝ)^256 := by
      have hnat : (1101 : ℕ)^1061*1250000000000000000^256 ≤ 133526545173547^256*10000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1101 10000 133526545173547 1250000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1101/10000 : ℝ)) (X := (133526545173547/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14667/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (4383141042654179/12500000000000000000 : ℝ) := by
    have hpowers : (14667/100000 : ℝ)^1061 ≤ (4383141042654179/12500000000000000000 : ℝ)^256 := by
      have hnat : (14667 : ℕ)^1061*12500000000000000000^256 ≤ 4383141042654179^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14667 100000 4383141042654179 12500000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14667/100000 : ℝ)) (X := (4383141042654179/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (625133526545173547/625000000000000000 : ℝ) ≤ (5000257719325097/5000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (625133526545173547/625000000000000000 : ℝ)^256 ≤ (5000257719325097/5000000000000000 : ℝ)^1061 := by
      have hnat : (625133526545173547 : ℕ)^256*5000000000000000^1061 ≤ 5000257719325097^1061*625000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625133526545173547 625000000000000000 5000257719325097 5000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000257719325097/5000000000000000 : ℝ)) (X := (625133526545173547/625000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505718406494389649/12500000000000000000 : ℝ) ≤ (2000220721292979/2000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (12505718406494389649/12500000000000000000 : ℝ)^256 ≤ (2000220721292979/2000000000000000 : ℝ)^1061 := by
      have hnat : (12505718406494389649 : ℕ)^256*2000000000000000^1061 ≤ 2000220721292979^1061*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505718406494389649 12500000000000000000 2000220721292979 2000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000220721292979/2000000000000000 : ℝ)) (X := (12505718406494389649/12500000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254383141042654179/6250000000000000000 : ℝ) ≤ (2500422943569899/2500000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (6254383141042654179/6250000000000000000 : ℝ)^256 ≤ (2500422943569899/2500000000000000 : ℝ)^1061 := by
      have hnat : (6254383141042654179 : ℕ)^256*2500000000000000^1061 ≤ 2500422943569899^1061*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254383141042654179 6250000000000000000 2500422943569899 2500000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500422943569899/2500000000000000 : ℝ)) (X := (6254383141042654179/6250000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(133526545173547/1250000000000000000 : ℝ) ≤ ((6093155583977340573/6095000000000000000 : ℝ)+2*(588167814701/365700000000000 : ℝ)*(1101/10000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (6093155583977340573/6095000000000000000 : ℝ)+2*(588167814701/365700000000000 : ℝ)*(1101/10000 : ℝ)=(5000257719325097/5000000000000000 : ℝ) by norm_num, show 1+2*(133526545173547/1250000000000000000 : ℝ)=(625133526545173547/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4383141042654179/12500000000000000000 : ℝ)+(133526545173547/1250000000000000000 : ℝ) ≤ ((6093155583977340573/6095000000000000000 : ℝ)+(588167814701/365700000000000 : ℝ)*((14667/100000 : ℝ)+(1101/10000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (6093155583977340573/6095000000000000000 : ℝ)+(588167814701/365700000000000 : ℝ)*((14667/100000 : ℝ)+(1101/10000 : ℝ))=(2000220721292979/2000000000000000 : ℝ) by norm_num, show 1+(4383141042654179/12500000000000000000 : ℝ)+(133526545173547/1250000000000000000 : ℝ)=(12505718406494389649/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4383141042654179/12500000000000000000 : ℝ) ≤ ((6093155583977340573/6095000000000000000 : ℝ)+2*(588167814701/365700000000000 : ℝ)*(14667/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (6093155583977340573/6095000000000000000 : ℝ)+2*(588167814701/365700000000000 : ℝ)*(14667/100000 : ℝ)=(2500422943569899/2500000000000000 : ℝ) by norm_num, show 1+2*(4383141042654179/12500000000000000000 : ℝ)=(6254383141042654179/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6093155583977340573/6095000000000000000 : ℝ)*(X 1 0+X 2 0)+(588167814701/365700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (6093155583977340573/6095000000000000000 : ℝ)) (alpha := (588167814701/365700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6093155583977340573/6095000000000000000 : ℝ)*(X 0 1+X 2 1)+(588167814701/365700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (6093155583977340573/6095000000000000000 : ℝ)) (alpha := (588167814701/365700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6093155583977340573/6095000000000000000 : ℝ)*(X 0 2+X 1 2)+(588167814701/365700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (1101/10000 : ℝ)) (hi := (14667/100000 : ℝ)) (c := (6093155583977340573/6095000000000000000 : ℝ)) (alpha := (588167814701/365700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1922325957/10000000000 : ℝ)*X 0 0+(5392299407/10000000000 : ℝ)*X 0 1+(5392299609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330264979/625000000 : ℝ)*X 1 0+(-258758147/1250000000 : ℝ)*X 1 1+(674037449/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642119843/5000000000 : ℝ)*X 2 0+(674037429/1250000000 : ℝ)*X 2 1+(-2070065363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4491357723/10000000000 : ℝ)*X 0 0+(2135484413/5000000000 : ℝ)*X 0 1+(427096867/1000000000 : ℝ)*X 0 2+(4491357723/10000000000 : ℝ)*X 1 0+(2135484413/5000000000 : ℝ)*X 1 1+(427096867/1000000000 : ℝ)*X 1 2+(4491357723/10000000000 : ℝ)*X 2 0+(2135484413/5000000000 : ℝ)*X 2 1+(427096867/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1134481393/5000000000 : ℝ)*X 0 0+(5263502149/10000000000 : ℝ)*X 0 1+(5263501183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343731271/2500000000 : ℝ)*X 1 0+(-2121325193/10000000000 : ℝ)*X 1 1+(5263502537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671865657/1250000000 : ℝ)*X 2 0+(526350243/1000000000 : ℝ)*X 2 1+(-424265021/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4191302881/10000000000 : ℝ)*X 0 0+(884188089/2000000000 : ℝ)*X 0 1+(552617579/1250000000 : ℝ)*X 0 2+(4191302881/10000000000 : ℝ)*X 1 0+(884188089/2000000000 : ℝ)*X 1 1+(552617579/1250000000 : ℝ)*X 1 2+(4191302881/10000000000 : ℝ)*X 2 0+(884188089/2000000000 : ℝ)*X 2 1+(552617579/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1098166191/5000000000 : ℝ)*X 0 0+(5175112071/10000000000 : ℝ)*X 0 1+(1351584891/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274348161/10000000000 : ℝ)*X 1 0+(-2064340551/10000000000 : ℝ)*X 1 1+(2703169737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274347827/10000000000 : ℝ)*X 2 0+(2703169639/5000000000 : ℝ)*X 2 1+(-2064341267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4523505479/10000000000 : ℝ)*X 0 0+(2127303821/5000000000 : ℝ)*X 0 1+(425460669/1000000000 : ℝ)*X 0 2+(4523505479/10000000000 : ℝ)*X 1 0+(2127303821/5000000000 : ℝ)*X 1 1+(425460669/1000000000 : ℝ)*X 1 2+(4523505479/10000000000 : ℝ)*X 2 0+(2127303821/5000000000 : ℝ)*X 2 1+(425460669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-997705211/5000000000 : ℝ)*X 0 0+(2739173991/5000000000 : ℝ)*X 0 1+(2626243091/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((215307159/400000000 : ℝ)*X 1 0+(-1062801473/5000000000 : ℝ)*X 1 1+(2626242981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((336417433/625000000 : ℝ)*X 2 0+(2626243079/5000000000 : ℝ)*X 2 1+(-2125602747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((260324651/625000000 : ℝ)*X 0 0+(4433756937/10000000000 : ℝ)*X 0 1+(2216878169/5000000000 : ℝ)*X 0 2+(260324651/625000000 : ℝ)*X 1 0+(4433756937/10000000000 : ℝ)*X 1 1+(2216878169/5000000000 : ℝ)*X 1 2+(260324651/625000000 : ℝ)*X 2 0+(4433756937/10000000000 : ℝ)*X 2 1+(2216878169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31419/50000 : ℝ) ≤ (-374003733553026230461552104927/595214843750000000000000000000 : ℝ) := by norm_num
    linear_combination (38975987/100000000000000 : ℝ)*(upper1) + (34719/20000000000000 : ℝ)*(upper4) + (18062801/12500000000000 : ℝ)*(upper5) + (357009142206219/12500000000000 : ℝ)*(major0) + (357009142206219/12500000000000 : ℝ)*(major1) + (357009142206219/12500000000000 : ℝ)*(major2) + (9150454107/100000000000000 : ℝ)*(sp3) + (1930037912585737/50000000000000 : ℝ)*(sp4) + (1929935086197699/50000000000000 : ℝ)*(sp5) + (482494446347041/12500000000000 : ℝ)*(sp6) + (234123068541987/12500000000000 : ℝ)*(sp7) + (10889291059/50000000000000 : ℝ)*(sp8) + (113715679097/50000000000000 : ℝ)*(sp13) + (8877061079/6250000000000 : ℝ)*(sp14) + (936496849395001/50000000000000 : ℝ)*(f.failure) + (482512200469199/12500000000000 : ℝ)*(f.sum) + (5720085925169/6095000000000000000000000000 : ℝ)*base65 + (239759328869398487/76187500000000000000000000000000 : ℝ)*base67 + (262468530183726513/76187500000000000000000000000000 : ℝ)*base70 + (365309850921039013/76187500000000000000000000000000 : ℝ)*base72 + (11757453986201/1523750000000000000000000000 : ℝ)*base73 + (291086616817476513/76187500000000000000000000000000 : ℝ)*base76 + (8439858594914013/76187500000000000000000000000000 : ℝ)*base78 + (391388949118851513/76187500000000000000000000000000 : ℝ)*base80 + (1100403368723/3047500000000000000000000000 : ℝ)*base82 + (11221467/2500000000000000000000 : ℝ)*base90 + (11221467/2500000000000000000000 : ℝ)*base92 + (11221467/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (3677/6250 : ℝ) ≤ (8964871801987911448601809339591/15237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21659271/50000000000000 : ℝ)*(lower0) + (1045533/25000000000000 : ℝ)*(upper1) + (55521161/100000000000000 : ℝ)*(upper2) + (583141/3125000000000 : ℝ)*(upper3) + (146143014311011/5000000000000 : ℝ)*(major0) + (146143014311011/5000000000000 : ℝ)*(major1) + (146143014311011/5000000000000 : ℝ)*(major2) + (244332087749239/6250000000000 : ℝ)*(sp0) + (3909314746423771/100000000000000 : ℝ)*(sp1) + (977317915248393/25000000000000 : ℝ)*(sp2) + (1916792265004443/100000000000000 : ℝ)*(sp3) + (2137874149/100000000000000 : ℝ)*(sp5) + (45223304349/100000000000000 : ℝ)*(sp10) + (217519381/6250000000000 : ℝ)*(sp12) + (1916792265004443/100000000000000 : ℝ)*(f.failure) + (12216615263431/312500000000 : ℝ)*(f.sum) + (102800574588469/3657000000000000000000000000 : ℝ)*base66 + (270546861693247909/91425000000000000000000000000000 : ℝ)*base67 + (1073878722373747909/91425000000000000000000000000000 : ℝ)*base69 + (340100332906072909/91425000000000000000000000000000 : ℝ)*base71 + (53639799227339/3657000000000000000000000000 : ℝ)*base73 + (1059290660745022909/91425000000000000000000000000000 : ℝ)*base75 + (1625097555009802091/91425000000000000000000000000000 : ℝ)*base78 + (813015334439302091/91425000000000000000000000000000 : ℝ)*base80 + (24464163535757/3657000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4982881/5000000000000000000000 : ℝ)*base90 + (4982881/5000000000000000000000 : ℝ)*base92 + (4982881/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (39807/50000 : ℝ) ≤ (30328879183050695490135460782631/38093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123656161/50000000000000 : ℝ)*(upper1) + (139672877/50000000000000 : ℝ)*(upper2) + (46588681/25000000000000 : ℝ)*(lower5) + (809266349688851/25000000000000 : ℝ)*(major0) + (809266349688851/25000000000000 : ℝ)*(major1) + (809266349688851/25000000000000 : ℝ)*(major2) + (44351977849/25000000000000 : ℝ)*(sp1) + (4102752997/10000000000000 : ℝ)*(sp2) + (30648105151/50000000000000 : ℝ)*(sp3) + (2848604553/100000000000000 : ℝ)*(sp4) + (2162371631264129/50000000000000 : ℝ)*(sp8) + (864913740644283/20000000000000 : ℝ)*(sp9) + (108117627090071/2500000000000 : ℝ)*(sp10) + (530696146052601/25000000000000 : ℝ)*(sp11) + (2122845880420707/100000000000000 : ℝ)*(f.failure) + (432474611113281/10000000000000 : ℝ)*(f.sum) + (60458542073881/4571250000000000000000000000 : ℝ)*base65 + (8983167166514829869/457125000000000000000000000000000 : ℝ)*base67 + (308212629526670131/457125000000000000000000000000000 : ℝ)*base70 + (4301519154077079869/457125000000000000000000000000000 : ℝ)*base71 + (182827434506389/18285000000000000000000000000 : ℝ)*base73 + (3992647735952454869/457125000000000000000000000000000 : ℝ)*base75 + (10065161732822454869/457125000000000000000000000000000 : ℝ)*base77 + (6735373902369204869/457125000000000000000000000000000 : ℝ)*base79 + (48441167353427/9142500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (28037831/5000000000000000000000 : ℝ)*base89 + (28037831/5000000000000000000000 : ℝ)*base91 + (28037831/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84127/100000 : ℝ) ≤ (-256369206484636951185476524249557/304750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19684569/25000000000000 : ℝ)*(lower0) + (39871153/50000000000000 : ℝ)*(lower2) + (3438151/20000000000000 : ℝ)*(upper3) + (1636447549678099/50000000000000 : ℝ)*(major0) + (1636447549678099/50000000000000 : ℝ)*(major1) + (3272895099356199/100000000000000 : ℝ)*(major2) + (7936737617/100000000000000 : ℝ)*(sp0) + (102373814109/50000000000000 : ℝ)*(sp5) + (15014195737/20000000000000 : ℝ)*(sp6) + (40359839853/100000000000000 : ℝ)*(sp7) + (553435122550027/12500000000000 : ℝ)*(sp12) + (2213642084754807/50000000000000 : ℝ)*(sp13) + (4427413846159147/100000000000000 : ℝ)*(sp14) + (214630239906417/10000000000000 : ℝ)*(sp15) + (2146342758904023/100000000000000 : ℝ)*(f.failure) + (553436114642229/12500000000000 : ℝ)*(f.sum) + (6212493651143/36570000000000000000000000000 : ℝ)*base66 + (998633233965464273/304750000000000000000000000000000 : ℝ)*base68 + (1305489158273313919/1828500000000000000000000000000000 : ℝ)*base70 + (313682640493214273/304750000000000000000000000000000 : ℝ)*base72 + (437415712810807/36570000000000000000000000000 : ℝ)*base73 + (1086655501539813919/1828500000000000000000000000000000 : ℝ)*base76 + (7504467099046667819/914250000000000000000000000000000 : ℝ)*base78 + (13885984469969832181/914250000000000000000000000000000 : ℝ)*base79 + (7579475251033/1142812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (21433259/5000000000000000000000 : ℝ)*base89 + (21433259/5000000000000000000000 : ℝ)*base91 + (28566741/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1285_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14667/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3677/6250 : ℝ) else (39807/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84127/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1285_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1285_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3677/6250 : ℝ) else (39807/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84127/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1285_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1285_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1285_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(3677/6250 : ℝ) else (39807/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84127/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
