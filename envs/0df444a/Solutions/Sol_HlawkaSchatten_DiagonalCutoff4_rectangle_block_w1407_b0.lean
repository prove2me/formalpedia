-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1407_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:58.805122+00:00
-- url     : https://prove2.me/submissions/43e81ef5-61ce-4741-9ade-4fb144a4609b

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
theorem support_rectangle_w1407_s0_0 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1771337041/10000000000 : ℝ)*x 0 + (2984656339/5000000000 : ℝ)*x 1 + (4826178811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1771337041/10000000000 : ℝ)^4367 ≤ (5212152039849/50000000000000 : ℝ)^3343 := by
    have hnat : (1771337041 : ℕ)^4367*50000000000000^3343 ≤ 5212152039849^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771337041 10000000000 5212152039849 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2984656339/5000000000 : ℝ)^4367 ≤ (10193359115363/20000000000000 : ℝ)^3343 := by
    have hnat : (2984656339 : ℕ)^4367*20000000000000^3343 ≤ 10193359115363^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2984656339 5000000000 10193359115363 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4826178811/10000000000 : ℝ)^4367 ≤ (19304450161787/50000000000000 : ℝ)^3343 := by
    have hnat : (4826178811 : ℕ)^4367*50000000000000^3343 ≤ 19304450161787^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826178811 10000000000 19304450161787 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1771337041/10000000000 : ℝ), (2984656339/5000000000 : ℝ), (4826178811/10000000000 : ℝ)] ![(5212152039849/50000000000000 : ℝ), (10193359115363/20000000000000 : ℝ), (19304450161787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1771337041/10000000000 : ℝ)|^4367 ≤ (5212152039849/50000000000000 : ℝ)^3343
        have hw : |(-1771337041/10000000000 : ℝ)|=(1771337041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2984656339/5000000000 : ℝ)|^4367 ≤ (10193359115363/20000000000000 : ℝ)^3343
        have hw : |(2984656339/5000000000 : ℝ)|=(2984656339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4826178811/10000000000 : ℝ)|^4367 ≤ (19304450161787/50000000000000 : ℝ)^3343
        have hw : |(4826178811/10000000000 : ℝ)|=(4826178811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_1 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (686818607/1250000000 : ℝ)*x 0 + (-2418080723/10000000000 : ℝ)*x 1 + (603272387/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686818607/1250000000 : ℝ)^4367 ≤ (914745279289/2000000000000 : ℝ)^3343 := by
    have hnat : (686818607 : ℕ)^4367*2000000000000^3343 ≤ 914745279289^3343*1250000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686818607 1250000000 914745279289 2000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2418080723/10000000000 : ℝ)^4367 ≤ (7826916356321/50000000000000 : ℝ)^3343 := by
    have hnat : (2418080723 : ℕ)^4367*50000000000000^3343 ≤ 7826916356321^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2418080723 10000000000 7826916356321 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603272387/1250000000 : ℝ)^4367 ≤ (9652225825481/25000000000000 : ℝ)^3343 := by
    have hnat : (603272387 : ℕ)^4367*25000000000000^3343 ≤ 9652225825481^3343*1250000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603272387 1250000000 9652225825481 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(686818607/1250000000 : ℝ), (-2418080723/10000000000 : ℝ), (603272387/1250000000 : ℝ)] ![(914745279289/2000000000000 : ℝ), (7826916356321/50000000000000 : ℝ), (9652225825481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(686818607/1250000000 : ℝ)|^4367 ≤ (914745279289/2000000000000 : ℝ)^3343
        have hw : |(686818607/1250000000 : ℝ)|=(686818607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2418080723/10000000000 : ℝ)|^4367 ≤ (7826916356321/50000000000000 : ℝ)^3343
        have hw : |(-2418080723/10000000000 : ℝ)|=(2418080723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603272387/1250000000 : ℝ)|^4367 ≤ (9652225825481/25000000000000 : ℝ)^3343
        have hw : |(603272387/1250000000 : ℝ)|=(603272387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_2 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2747274533/5000000000 : ℝ)*x 0 + (4826178979/10000000000 : ℝ)*x 1 + (-1209040299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2747274533/5000000000 : ℝ)^4367 ≤ (45737266247967/100000000000000 : ℝ)^3343 := by
    have hnat : (2747274533 : ℕ)^4367*100000000000000^3343 ≤ 45737266247967^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747274533 5000000000 45737266247967 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826178979/10000000000 : ℝ)^4367 ≤ (38608902079233/100000000000000 : ℝ)^3343 := by
    have hnat : (4826178979 : ℕ)^4367*100000000000000^3343 ≤ 38608902079233^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826178979 10000000000 38608902079233 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209040299/5000000000 : ℝ)^4367 ≤ (3913457913891/25000000000000 : ℝ)^3343 := by
    have hnat : (1209040299 : ℕ)^4367*25000000000000^3343 ≤ 3913457913891^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209040299 5000000000 3913457913891 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2747274533/5000000000 : ℝ), (4826178979/10000000000 : ℝ), (-1209040299/5000000000 : ℝ)] ![(45737266247967/100000000000000 : ℝ), (38608902079233/100000000000000 : ℝ), (3913457913891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2747274533/5000000000 : ℝ)|^4367 ≤ (45737266247967/100000000000000 : ℝ)^3343
        have hw : |(2747274533/5000000000 : ℝ)|=(2747274533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826178979/10000000000 : ℝ)|^4367 ≤ (38608902079233/100000000000000 : ℝ)^3343
        have hw : |(4826178979/10000000000 : ℝ)|=(4826178979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1209040299/5000000000 : ℝ)|^4367 ≤ (3913457913891/25000000000000 : ℝ)^3343
        have hw : |(-1209040299/5000000000 : ℝ)|=(1209040299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_3 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042293231/2500000000 : ℝ)*x 0 + (1551982733/5000000000 : ℝ)*x 1 + (5557027211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042293231/2500000000 : ℝ)^4367 ≤ (15945449119119/50000000000000 : ℝ)^3343 := by
    have hnat : (1042293231 : ℕ)^4367*50000000000000^3343 ≤ 15945449119119^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042293231 2500000000 15945449119119 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551982733/5000000000 : ℝ)^4367 ≤ (5422818730217/25000000000000 : ℝ)^3343 := by
    have hnat : (1551982733 : ℕ)^4367*25000000000000^3343 ≤ 5422818730217^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551982733 5000000000 5422818730217 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5557027211/10000000000 : ℝ)^4367 ≤ (1856713073129/4000000000000 : ℝ)^3343 := by
    have hnat : (5557027211 : ℕ)^4367*4000000000000^3343 ≤ 1856713073129^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557027211 10000000000 1856713073129 4000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042293231/2500000000 : ℝ), (1551982733/5000000000 : ℝ), (5557027211/10000000000 : ℝ)] ![(15945449119119/50000000000000 : ℝ), (5422818730217/25000000000000 : ℝ), (1856713073129/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042293231/2500000000 : ℝ)|^4367 ≤ (15945449119119/50000000000000 : ℝ)^3343
        have hw : |(1042293231/2500000000 : ℝ)|=(1042293231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551982733/5000000000 : ℝ)|^4367 ≤ (5422818730217/25000000000000 : ℝ)^3343
        have hw : |(1551982733/5000000000 : ℝ)|=(1551982733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5557027211/10000000000 : ℝ)|^4367 ≤ (1856713073129/4000000000000 : ℝ)^3343
        have hw : |(5557027211/10000000000 : ℝ)|=(5557027211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_4 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1775461563/10000000000 : ℝ)*x 0 + (4855474847/10000000000 : ℝ)*x 1 + (2969485227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1775461563/10000000000 : ℝ)^4367 ≤ (10456023195617/100000000000000 : ℝ)^3343 := by
    have hnat : (1775461563 : ℕ)^4367*100000000000000^3343 ≤ 10456023195617^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775461563 10000000000 10456023195617 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4855474847/10000000000 : ℝ)^4367 ≤ (19457669192811/50000000000000 : ℝ)^3343 := by
    have hnat : (4855474847 : ℕ)^4367*50000000000000^3343 ≤ 19457669192811^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4855474847 10000000000 19457669192811 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2969485227/5000000000 : ℝ)^4367 ≤ (12657159601857/25000000000000 : ℝ)^3343 := by
    have hnat : (2969485227 : ℕ)^4367*25000000000000^3343 ≤ 12657159601857^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969485227 5000000000 12657159601857 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1775461563/10000000000 : ℝ), (4855474847/10000000000 : ℝ), (2969485227/5000000000 : ℝ)] ![(10456023195617/100000000000000 : ℝ), (19457669192811/50000000000000 : ℝ), (12657159601857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1775461563/10000000000 : ℝ)|^4367 ≤ (10456023195617/100000000000000 : ℝ)^3343
        have hw : |(-1775461563/10000000000 : ℝ)|=(1775461563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4855474847/10000000000 : ℝ)|^4367 ≤ (19457669192811/50000000000000 : ℝ)^3343
        have hw : |(4855474847/10000000000 : ℝ)|=(4855474847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2969485227/5000000000 : ℝ)|^4367 ≤ (12657159601857/25000000000000 : ℝ)^3343
        have hw : |(2969485227/5000000000 : ℝ)|=(2969485227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_5 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259132353/500000000 : ℝ)*x 0 + (-130528973/1000000000 : ℝ)*x 1 + (296948509/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259132353/500000000 : ℝ)^4367 ≤ (21187780520423/50000000000000 : ℝ)^3343 := by
    have hnat : (259132353 : ℕ)^4367*50000000000000^3343 ≤ 21187780520423^3343*500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259132353 500000000 21187780520423 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130528973/1000000000 : ℝ)^4367 ≤ (874475449067/12500000000000 : ℝ)^3343 := by
    have hnat : (130528973 : ℕ)^4367*12500000000000^3343 ≤ 874475449067^3343*1000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130528973 1000000000 874475449067 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296948509/500000000 : ℝ)^4367 ≤ (10125727071229/20000000000000 : ℝ)^3343 := by
    have hnat : (296948509 : ℕ)^4367*20000000000000^3343 ≤ 10125727071229^3343*500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296948509 500000000 10125727071229 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259132353/500000000 : ℝ), (-130528973/1000000000 : ℝ), (296948509/500000000 : ℝ)] ![(21187780520423/50000000000000 : ℝ), (874475449067/12500000000000 : ℝ), (10125727071229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259132353/500000000 : ℝ)|^4367 ≤ (21187780520423/50000000000000 : ℝ)^3343
        have hw : |(259132353/500000000 : ℝ)|=(259132353/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130528973/1000000000 : ℝ)|^4367 ≤ (874475449067/12500000000000 : ℝ)^3343
        have hw : |(-130528973/1000000000 : ℝ)|=(130528973/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(296948509/500000000 : ℝ)|^4367 ≤ (10125727071229/20000000000000 : ℝ)^3343
        have hw : |(296948509/500000000 : ℝ)|=(296948509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_6 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518264717/1000000000 : ℝ)*x 0 + (5938970617/10000000000 : ℝ)*x 1 + (-652644433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518264717/1000000000 : ℝ)^4367 ≤ (5296945276969/12500000000000 : ℝ)^3343 := by
    have hnat : (518264717 : ℕ)^4367*12500000000000^3343 ≤ 5296945276969^3343*1000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518264717 1000000000 5296945276969 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5938970617/10000000000 : ℝ)^4367 ≤ (50628640222607/100000000000000 : ℝ)^3343 := by
    have hnat : (5938970617 : ℕ)^4367*100000000000000^3343 ≤ 50628640222607^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938970617 10000000000 50628640222607 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652644433/5000000000 : ℝ)^4367 ≤ (6995797543429/100000000000000 : ℝ)^3343 := by
    have hnat : (652644433 : ℕ)^4367*100000000000000^3343 ≤ 6995797543429^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652644433 5000000000 6995797543429 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518264717/1000000000 : ℝ), (5938970617/10000000000 : ℝ), (-652644433/5000000000 : ℝ)] ![(5296945276969/12500000000000 : ℝ), (50628640222607/100000000000000 : ℝ), (6995797543429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518264717/1000000000 : ℝ)|^4367 ≤ (5296945276969/12500000000000 : ℝ)^3343
        have hw : |(518264717/1000000000 : ℝ)|=(518264717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5938970617/10000000000 : ℝ)|^4367 ≤ (50628640222607/100000000000000 : ℝ)^3343
        have hw : |(5938970617/10000000000 : ℝ)|=(5938970617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-652644433/5000000000 : ℝ)|^4367 ≤ (6995797543429/100000000000000 : ℝ)^3343
        have hw : |(-652644433/5000000000 : ℝ)|=(652644433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s0_7 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044506431/2500000000 : ℝ)*x 0 + (5494160191/10000000000 : ℝ)*x 1 + (3169077923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044506431/2500000000 : ℝ)^4367 ≤ (15989693228819/50000000000000 : ℝ)^3343 := by
    have hnat : (1044506431 : ℕ)^4367*50000000000000^3343 ≤ 15989693228819^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044506431 2500000000 15989693228819 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494160191/10000000000 : ℝ)^4367 ≤ (178644678553/390625000000 : ℝ)^3343 := by
    have hnat : (5494160191 : ℕ)^4367*390625000000^3343 ≤ 178644678553^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494160191 10000000000 178644678553 390625000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169077923/10000000000 : ℝ)^4367 ≤ (2785946977689/12500000000000 : ℝ)^3343 := by
    have hnat : (3169077923 : ℕ)^4367*12500000000000^3343 ≤ 2785946977689^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169077923 10000000000 2785946977689 12500000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044506431/2500000000 : ℝ), (5494160191/10000000000 : ℝ), (3169077923/10000000000 : ℝ)] ![(15989693228819/50000000000000 : ℝ), (178644678553/390625000000 : ℝ), (2785946977689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044506431/2500000000 : ℝ)|^4367 ≤ (15989693228819/50000000000000 : ℝ)^3343
        have hw : |(1044506431/2500000000 : ℝ)|=(1044506431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494160191/10000000000 : ℝ)|^4367 ≤ (178644678553/390625000000 : ℝ)^3343
        have hw : |(5494160191/10000000000 : ℝ)|=(5494160191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169077923/10000000000 : ℝ)|^4367 ≤ (2785946977689/12500000000000 : ℝ)^3343
        have hw : |(3169077923/10000000000 : ℝ)|=(3169077923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1407_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26411/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2183/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2183 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2183*1^512 ≤ 0^512*1^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2183/512 : ℝ) ≤ (2010547681217282671/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2183 ≤ (2010547681217282671/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2183*100000000000000000000^512 ≤ 2010547681217282671^512*5^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2010547681217282671 100000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2010547681217282671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2183 := by
      have hnat : (1 : ℕ)^512*1^2183 ≤ 1^2183*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102010547681217282671/100000000000000000000 : ℝ) ≤ (5023398342724567/5000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (102010547681217282671/100000000000000000000 : ℝ)^512 ≤ (5023398342724567/5000000000000000 : ℝ)^2183 := by
      have hnat : (102010547681217282671 : ℕ)^512*5000000000000000^2183 ≤ 5023398342724567^2183*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102010547681217282671 100000000000000000000 5023398342724567 5000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023398342724567/5000000000000000 : ℝ)) (X := (102010547681217282671/100000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52010547681217282671/50000000000000000000 : ℝ) ≤ (2523398342724567/2500000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (52010547681217282671/50000000000000000000 : ℝ)^512 ≤ (2523398342724567/2500000000000000 : ℝ)^2183 := by
      have hnat : (52010547681217282671 : ℕ)^512*2500000000000000^2183 ≤ 2523398342724567^2183*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52010547681217282671 50000000000000000000 2523398342724567 2500000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523398342724567/2500000000000000 : ℝ)) (X := (52010547681217282671/50000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(23398342724567/2000000000000000 : ℝ)*(0 : ℝ))^(2183/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(23398342724567/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2010547681217282671/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(23398342724567/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2183/512 : ℝ) := by
    rw [show (1 : ℝ)+(23398342724567/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5023398342724567/5000000000000000 : ℝ) by norm_num, show 1+(2010547681217282671/100000000000000000000 : ℝ)+(0 : ℝ)=(102010547681217282671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2010547681217282671/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(23398342724567/2000000000000000 : ℝ)*(2/5 : ℝ))^(2183/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(23398342724567/2000000000000000 : ℝ)*(2/5 : ℝ)=(2523398342724567/2500000000000000 : ℝ) by norm_num, show 1+2*(2010547681217282671/100000000000000000000 : ℝ)=(52010547681217282671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(23398342724567/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23398342724567/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(23398342724567/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23398342724567/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(23398342724567/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23398342724567/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1771337041/10000000000 : ℝ)*X 0 0+(2984656339/5000000000 : ℝ)*X 0 1+(4826178811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((686818607/1250000000 : ℝ)*X 1 0+(-2418080723/10000000000 : ℝ)*X 1 1+(603272387/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2747274533/5000000000 : ℝ)*X 2 0+(4826178979/10000000000 : ℝ)*X 2 1+(-1209040299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042293231/2500000000 : ℝ)*X 0 0+(1551982733/5000000000 : ℝ)*X 0 1+(5557027211/10000000000 : ℝ)*X 0 2+(1042293231/2500000000 : ℝ)*X 1 0+(1551982733/5000000000 : ℝ)*X 1 1+(5557027211/10000000000 : ℝ)*X 1 2+(1042293231/2500000000 : ℝ)*X 2 0+(1551982733/5000000000 : ℝ)*X 2 1+(5557027211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1775461563/10000000000 : ℝ)*X 0 0+(4855474847/10000000000 : ℝ)*X 0 1+(2969485227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((259132353/500000000 : ℝ)*X 1 0+(-130528973/1000000000 : ℝ)*X 1 1+(296948509/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((518264717/1000000000 : ℝ)*X 2 0+(5938970617/10000000000 : ℝ)*X 2 1+(-652644433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044506431/2500000000 : ℝ)*X 0 0+(5494160191/10000000000 : ℝ)*X 0 1+(3169077923/10000000000 : ℝ)*X 0 2+(1044506431/2500000000 : ℝ)*X 1 0+(5494160191/10000000000 : ℝ)*X 1 1+(3169077923/10000000000 : ℝ)*X 1 2+(1044506431/2500000000 : ℝ)*X 2 0+(5494160191/10000000000 : ℝ)*X 2 1+(3169077923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70464894957857758440189/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265820837/20000000000000 : ℝ)*(base19) + (679073057/50000000000000 : ℝ)*(base23) + (153932529/100000000000000 : ℝ)*(upper3) + (2413493/100000000000000 : ℝ)*(upper4) + (48363791/25000000000000 : ℝ)*(upper5) + (160307026691611/25000000000000 : ℝ)*(major0) + (160307026691611/25000000000000 : ℝ)*(major1) + (160307026691611/25000000000000 : ℝ)*(major2) + (437396319456883/50000000000000 : ℝ)*(sp0) + (874796330101649/100000000000000 : ℝ)*(sp1) + (874796301059721/100000000000000 : ℝ)*(sp2) + (407656079330817/100000000000000 : ℝ)*(sp3) + (5020292069/100000000000000 : ℝ)*(sp4) + (2287089841/100000000000000 : ℝ)*(sp7) + (203829183210329/50000000000000 : ℝ)*(f.failure) + (437398829602917/50000000000000 : ℝ)*(f.sum) + (78907359032437/25000000000000000000000000000 : ℝ)*base65 + (334677134692563/50000000000000000000000000000 : ℝ)*base68 + (147243663407437/50000000000000000000000000000 : ℝ)*base69 + (76671205707437/50000000000000000000000000000 : ℝ)*base71 + (74454005642563/25000000000000000000000000000 : ℝ)*base74 + (437644275807437/50000000000000000000000000000 : ℝ)*base75 + (28965853607437/50000000000000000000000000000 : ℝ)*base77 + (122586688092563/50000000000000000000000000000 : ℝ)*base80 + (134589110707437/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (39983331/5000000000000000000000 : ℝ)*base90 + (39983331/5000000000000000000000 : ℝ)*base92 + (39983331/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (437703050032379467856571/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (917620943/50000000000000 : ℝ)*(base19) + (383867069/20000000000000 : ℝ)*(base23) + (234731201/100000000000000 : ℝ)*(base32) + (143358583/50000000000000 : ℝ)*(upper3) + (164480097/100000000000000 : ℝ)*(upper5) + (338257547163871/50000000000000 : ℝ)*(major0) + (338257547163871/50000000000000 : ℝ)*(major1) + (338257547163871/50000000000000 : ℝ)*(major2) + (3893736591/100000000000000 : ℝ)*(sp1) + (993111747/20000000000000 : ℝ)*(sp2) + (115367245037327/12500000000000 : ℝ)*(sp4) + (922932231320139/100000000000000 : ℝ)*(sp5) + (115366384425567/12500000000000 : ℝ)*(sp6) + (215045850911813/50000000000000 : ℝ)*(sp7) + (215045968277413/50000000000000 : ℝ)*(f.failure) + (115367245037327/12500000000000 : ℝ)*(f.sum) + (81565154281143/50000000000000000000000000000 : ℝ)*base66 + (227060665281143/100000000000000000000000000000 : ℝ)*base68 + (696127720318857/100000000000000000000000000000 : ℝ)*base69 + (69170879481143/100000000000000000000000000000 : ℝ)*base72 + (117960473631143/50000000000000000000000000000 : ℝ)*base74 + (403341211118857/100000000000000000000000000000 : ℝ)*base75 + (459186781118857/100000000000000000000000000000 : ℝ)*base77 + (421304517781143/100000000000000000000000000000 : ℝ)*base80 + (171038311918857/50000000000000000000000000000 : ℝ)*base81 + (46277607/5000000000000000000000 : ℝ)*base90 + (46277607/5000000000000000000000 : ℝ)*base92 + (46277607/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1407_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26411/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1407_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1407_s1_0 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-973409571/5000000000 : ℝ)*x 0 + (5614174413/10000000000 : ℝ)*x 1 + (2534427529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973409571/5000000000 : ℝ)^4367 ≤ (11793364710381/100000000000000 : ℝ)^3343 := by
    have hnat : (973409571 : ℕ)^4367*100000000000000^3343 ≤ 11793364710381^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973409571 5000000000 11793364710381 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5614174413/10000000000 : ℝ)^4367 ≤ (47042374990667/100000000000000 : ℝ)^3343 := by
    have hnat : (5614174413 : ℕ)^4367*100000000000000^3343 ≤ 47042374990667^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614174413 10000000000 47042374990667 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2534427529/5000000000 : ℝ)^4367 ≤ (20582130141183/50000000000000 : ℝ)^3343 := by
    have hnat : (2534427529 : ℕ)^4367*50000000000000^3343 ≤ 20582130141183^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534427529 5000000000 20582130141183 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973409571/5000000000 : ℝ), (5614174413/10000000000 : ℝ), (2534427529/5000000000 : ℝ)] ![(11793364710381/100000000000000 : ℝ), (47042374990667/100000000000000 : ℝ), (20582130141183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973409571/5000000000 : ℝ)|^4367 ≤ (11793364710381/100000000000000 : ℝ)^3343
        have hw : |(-973409571/5000000000 : ℝ)|=(973409571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5614174413/10000000000 : ℝ)|^4367 ≤ (47042374990667/100000000000000 : ℝ)^3343
        have hw : |(5614174413/10000000000 : ℝ)|=(5614174413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2534427529/5000000000 : ℝ)|^4367 ≤ (20582130141183/50000000000000 : ℝ)^3343
        have hw : |(2534427529/5000000000 : ℝ)|=(2534427529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_1 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399030761/10000000000 : ℝ)*x 0 + (-559067307/2500000000 : ℝ)*x 1 + (2534427849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399030761/10000000000 : ℝ)^4367 ≤ (2235069362599/5000000000000 : ℝ)^3343 := by
    have hnat : (5399030761 : ℕ)^4367*5000000000000^3343 ≤ 2235069362599^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399030761 10000000000 2235069362599 5000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559067307/2500000000 : ℝ)^4367 ≤ (14134345656931/100000000000000 : ℝ)^3343 := by
    have hnat : (559067307 : ℕ)^4367*100000000000000^3343 ≤ 14134345656931^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559067307 2500000000 14134345656931 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2534427849/5000000000 : ℝ)^4367 ≤ (41164267071857/100000000000000 : ℝ)^3343 := by
    have hnat : (2534427849 : ℕ)^4367*100000000000000^3343 ≤ 41164267071857^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2534427849 5000000000 41164267071857 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399030761/10000000000 : ℝ), (-559067307/2500000000 : ℝ), (2534427849/5000000000 : ℝ)] ![(2235069362599/5000000000000 : ℝ), (14134345656931/100000000000000 : ℝ), (41164267071857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399030761/10000000000 : ℝ)|^4367 ≤ (2235069362599/5000000000000 : ℝ)^3343
        have hw : |(5399030761/10000000000 : ℝ)|=(5399030761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-559067307/2500000000 : ℝ)|^4367 ≤ (14134345656931/100000000000000 : ℝ)^3343
        have hw : |(-559067307/2500000000 : ℝ)|=(559067307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2534427849/5000000000 : ℝ)|^4367 ≤ (41164267071857/100000000000000 : ℝ)^3343
        have hw : |(2534427849/5000000000 : ℝ)|=(2534427849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_2 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079806263/2000000000 : ℝ)*x 0 + (5068855327/10000000000 : ℝ)*x 1 + (-111813449/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079806263/2000000000 : ℝ)^4367 ≤ (22350696621921/50000000000000 : ℝ)^3343 := by
    have hnat : (1079806263 : ℕ)^4367*50000000000000^3343 ≤ 22350696621921^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079806263 2000000000 22350696621921 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5068855327/10000000000 : ℝ)^4367 ≤ (20582131568037/50000000000000 : ℝ)^3343 := by
    have hnat : (5068855327 : ℕ)^4367*50000000000000^3343 ≤ 20582131568037^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5068855327 10000000000 20582131568037 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111813449/500000000 : ℝ)^4367 ≤ (3533585902327/25000000000000 : ℝ)^3343 := by
    have hnat : (111813449 : ℕ)^4367*25000000000000^3343 ≤ 3533585902327^3343*500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111813449 500000000 3533585902327 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079806263/2000000000 : ℝ), (5068855327/10000000000 : ℝ), (-111813449/500000000 : ℝ)] ![(22350696621921/50000000000000 : ℝ), (20582131568037/50000000000000 : ℝ), (3533585902327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079806263/2000000000 : ℝ)|^4367 ≤ (22350696621921/50000000000000 : ℝ)^3343
        have hw : |(1079806263/2000000000 : ℝ)|=(1079806263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5068855327/10000000000 : ℝ)|^4367 ≤ (20582131568037/50000000000000 : ℝ)^3343
        have hw : |(5068855327/10000000000 : ℝ)|=(5068855327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-111813449/500000000 : ℝ)|^4367 ≤ (3533585902327/25000000000000 : ℝ)^3343
        have hw : |(-111813449/500000000 : ℝ)|=(111813449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_3 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140314173/5000000000 : ℝ)*x 0 + (3731557561/10000000000 : ℝ)*x 1 + (4901762403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140314173/5000000000 : ℝ)^4367 ≤ (33009121589411/100000000000000 : ℝ)^3343 := by
    have hnat : (2140314173 : ℕ)^4367*100000000000000^3343 ≤ 33009121589411^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140314173 5000000000 33009121589411 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731557561/10000000000 : ℝ)^4367 ≤ (5518043059531/20000000000000 : ℝ)^3343 := by
    have hnat : (3731557561 : ℕ)^4367*20000000000000^3343 ≤ 5518043059531^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731557561 10000000000 5518043059531 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4901762403/10000000000 : ℝ)^4367 ≤ (9850165774291/25000000000000 : ℝ)^3343 := by
    have hnat : (4901762403 : ℕ)^4367*25000000000000^3343 ≤ 9850165774291^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4901762403 10000000000 9850165774291 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140314173/5000000000 : ℝ), (3731557561/10000000000 : ℝ), (4901762403/10000000000 : ℝ)] ![(33009121589411/100000000000000 : ℝ), (5518043059531/20000000000000 : ℝ), (9850165774291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140314173/5000000000 : ℝ)|^4367 ≤ (33009121589411/100000000000000 : ℝ)^3343
        have hw : |(2140314173/5000000000 : ℝ)|=(2140314173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731557561/10000000000 : ℝ)|^4367 ≤ (5518043059531/20000000000000 : ℝ)^3343
        have hw : |(3731557561/10000000000 : ℝ)|=(3731557561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4901762403/10000000000 : ℝ)|^4367 ≤ (9850165774291/25000000000000 : ℝ)^3343
        have hw : |(4901762403/10000000000 : ℝ)|=(4901762403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_4 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-486812089/2500000000 : ℝ)*x 0 + (5075360727/10000000000 : ℝ)*x 1 + (1121511293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486812089/2500000000 : ℝ)^4367 ≤ (471870453377/4000000000000 : ℝ)^3343 := by
    have hnat : (486812089 : ℕ)^4367*4000000000000^3343 ≤ 471870453377^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486812089 2500000000 471870453377 4000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5075360727/10000000000 : ℝ)^4367 ≤ (8246657951029/20000000000000 : ℝ)^3343 := by
    have hnat : (5075360727 : ℕ)^4367*20000000000000^3343 ≤ 8246657951029^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5075360727 10000000000 8246657951029 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121511293/2000000000 : ℝ)^4367 ≤ (11742487223951/25000000000000 : ℝ)^3343 := by
    have hnat : (1121511293 : ℕ)^4367*25000000000000^3343 ≤ 11742487223951^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121511293 2000000000 11742487223951 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486812089/2500000000 : ℝ), (5075360727/10000000000 : ℝ), (1121511293/2000000000 : ℝ)] ![(471870453377/4000000000000 : ℝ), (8246657951029/20000000000000 : ℝ), (11742487223951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486812089/2500000000 : ℝ)|^4367 ≤ (471870453377/4000000000000 : ℝ)^3343
        have hw : |(-486812089/2500000000 : ℝ)|=(486812089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5075360727/10000000000 : ℝ)|^4367 ≤ (8246657951029/20000000000000 : ℝ)^3343
        have hw : |(5075360727/10000000000 : ℝ)|=(5075360727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121511293/2000000000 : ℝ)|^4367 ≤ (11742487223951/25000000000000 : ℝ)^3343
        have hw : |(1121511293/2000000000 : ℝ)|=(1121511293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_5 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256789291/10000000000 : ℝ)*x 0 + (-1697568511/10000000000 : ℝ)*x 1 + (1401889083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256789291/10000000000 : ℝ)^4367 ≤ (4316920128173/10000000000000 : ℝ)^3343 := by
    have hnat : (5256789291 : ℕ)^4367*10000000000000^3343 ≤ 4316920128173^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256789291 10000000000 4316920128173 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1697568511/10000000000 : ℝ)^4367 ≤ (1972170251831/20000000000000 : ℝ)^3343 := by
    have hnat : (1697568511 : ℕ)^4367*20000000000000^3343 ≤ 1972170251831^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697568511 10000000000 1972170251831 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401889083/2500000000 : ℝ)^4367 ≤ (4696994744053/10000000000000 : ℝ)^3343 := by
    have hnat : (1401889083 : ℕ)^4367*10000000000000^3343 ≤ 4696994744053^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401889083 2500000000 4696994744053 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256789291/10000000000 : ℝ), (-1697568511/10000000000 : ℝ), (1401889083/2500000000 : ℝ)] ![(4316920128173/10000000000000 : ℝ), (1972170251831/20000000000000 : ℝ), (4696994744053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256789291/10000000000 : ℝ)|^4367 ≤ (4316920128173/10000000000000 : ℝ)^3343
        have hw : |(5256789291/10000000000 : ℝ)|=(5256789291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1697568511/10000000000 : ℝ)|^4367 ≤ (1972170251831/20000000000000 : ℝ)^3343
        have hw : |(-1697568511/10000000000 : ℝ)|=(1697568511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401889083/2500000000 : ℝ)|^4367 ≤ (4696994744053/10000000000000 : ℝ)^3343
        have hw : |(1401889083/2500000000 : ℝ)|=(1401889083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_6 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256789897/10000000000 : ℝ)*x 0 + (2803778407/5000000000 : ℝ)*x 1 + (-21219587/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256789897/10000000000 : ℝ)^4367 ≤ (43169207782621/100000000000000 : ℝ)^3343 := by
    have hnat : (5256789897 : ℕ)^4367*100000000000000^3343 ≤ 43169207782621^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256789897 10000000000 43169207782621 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2803778407/5000000000 : ℝ)^4367 ≤ (11742488178633/25000000000000 : ℝ)^3343 := by
    have hnat : (2803778407 : ℕ)^4367*25000000000000^3343 ≤ 11742488178633^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803778407 5000000000 11742488178633 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21219587/125000000 : ℝ)^4367 ≤ (986083948999/10000000000000 : ℝ)^3343 := by
    have hnat : (21219587 : ℕ)^4367*10000000000000^3343 ≤ 986083948999^3343*125000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21219587 125000000 986083948999 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256789897/10000000000 : ℝ), (2803778407/5000000000 : ℝ), (-21219587/125000000 : ℝ)] ![(43169207782621/100000000000000 : ℝ), (11742488178633/25000000000000 : ℝ), (986083948999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256789897/10000000000 : ℝ)|^4367 ≤ (43169207782621/100000000000000 : ℝ)^3343
        have hw : |(5256789897/10000000000 : ℝ)|=(5256789897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2803778407/5000000000 : ℝ)|^4367 ≤ (11742488178633/25000000000000 : ℝ)^3343
        have hw : |(2803778407/5000000000 : ℝ)|=(2803778407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21219587/125000000 : ℝ)|^4367 ≤ (986083948999/10000000000000 : ℝ)^3343
        have hw : |(-21219587/125000000 : ℝ)|=(21219587/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s1_7 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140775457/5000000000 : ℝ)*x 0 + (4887800673/10000000000 : ℝ)*x 1 + (374575883/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140775457/5000000000 : ℝ)^4367 ≤ (6603683046461/20000000000000 : ℝ)^3343 := by
    have hnat : (2140775457 : ℕ)^4367*20000000000000^3343 ≤ 6603683046461^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140775457 5000000000 6603683046461 20000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4887800673/10000000000 : ℝ)^4367 ≤ (2453382872469/6250000000000 : ℝ)^3343 := by
    have hnat : (4887800673 : ℕ)^4367*6250000000000^3343 ≤ 2453382872469^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4887800673 10000000000 2453382872469 6250000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374575883/1000000000 : ℝ)^4367 ≤ (2772745878789/10000000000000 : ℝ)^3343 := by
    have hnat : (374575883 : ℕ)^4367*10000000000000^3343 ≤ 2772745878789^3343*1000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374575883 1000000000 2772745878789 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140775457/5000000000 : ℝ), (4887800673/10000000000 : ℝ), (374575883/1000000000 : ℝ)] ![(6603683046461/20000000000000 : ℝ), (2453382872469/6250000000000 : ℝ), (2772745878789/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140775457/5000000000 : ℝ)|^4367 ≤ (6603683046461/20000000000000 : ℝ)^3343
        have hw : |(2140775457/5000000000 : ℝ)|=(2140775457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4887800673/10000000000 : ℝ)|^4367 ≤ (2453382872469/6250000000000 : ℝ)^3343
        have hw : |(4887800673/10000000000 : ℝ)|=(4887800673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374575883/1000000000 : ℝ)|^4367 ≤ (2772745878789/10000000000000 : ℝ)^3343
        have hw : |(374575883/1000000000 : ℝ)|=(374575883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1407_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26411/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1867/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3799/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26411/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26411/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26411/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26411/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26411/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26411/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1891/100000 : ℝ) ^ (2183/512 : ℝ) ≤ (898272564111/20000000000000000000 : ℝ) := by
    have hpowers : (1891/100000 : ℝ)^2183 ≤ (898272564111/20000000000000000000 : ℝ)^512 := by
      have hnat : (1891 : ℕ)^2183*20000000000000000000^512 ≤ 898272564111^512*100000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1891 100000 898272564111 20000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1891/100000 : ℝ)) (X := (898272564111/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26411/100000 : ℝ) ^ (2183/512 : ℝ) ≤ (1712577804659493/500000000000000000 : ℝ) := by
    have hpowers : (26411/100000 : ℝ)^2183 ≤ (1712577804659493/500000000000000000 : ℝ)^512 := by
      have hnat : (26411 : ℕ)^2183*500000000000000000^512 ≤ 1712577804659493^512*100000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26411 100000 1712577804659493 500000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26411/100000 : ℝ)) (X := (1712577804659493/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000898272564111/10000000000000000000 : ℝ) ≤ (10000000210680503/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (10000000898272564111/10000000000000000000 : ℝ)^512 ≤ (10000000210680503/10000000000000000 : ℝ)^2183 := by
      have hnat : (10000000898272564111 : ℕ)^512*10000000000000000^2183 ≤ 10000000210680503^2183*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000898272564111 10000000000000000000 10000000210680503 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000210680503/10000000000000000 : ℝ)) (X := (10000000898272564111/10000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20068504010458943831/20000000000000000000 : ℝ) ≤ (2502005735585799/2500000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (20068504010458943831/20000000000000000000 : ℝ)^512 ≤ (2502005735585799/2500000000000000 : ℝ)^2183 := by
      have hnat : (20068504010458943831 : ℕ)^512*2500000000000000^2183 ≤ 2502005735585799^2183*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20068504010458943831 20000000000000000000 2502005735585799 2500000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502005735585799/2500000000000000 : ℝ)) (X := (20068504010458943831/20000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (251712577804659493/250000000000000000 : ℝ) ≤ (10016045674005889/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (251712577804659493/250000000000000000 : ℝ)^512 ≤ (10016045674005889/10000000000000000 : ℝ)^2183 := by
      have hnat : (251712577804659493 : ℕ)^512*10000000000000000^2183 ≤ 10016045674005889^2183*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251712577804659493 250000000000000000 10016045674005889 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016045674005889/10000000000000000 : ℝ)) (X := (251712577804659493/250000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(898272564111/20000000000000000000 : ℝ) ≤ ((122584831597368814317/122600000000000000000 : ℝ)+2*(8022731662693/2452000000000000 : ℝ)*(1891/100000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (122584831597368814317/122600000000000000000 : ℝ)+2*(8022731662693/2452000000000000 : ℝ)*(1891/100000 : ℝ)=(10000000210680503/10000000000000000 : ℝ) by norm_num, show 1+2*(898272564111/20000000000000000000 : ℝ)=(10000000898272564111/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1712577804659493/500000000000000000 : ℝ)+(898272564111/20000000000000000000 : ℝ) ≤ ((122584831597368814317/122600000000000000000 : ℝ)+(8022731662693/2452000000000000 : ℝ)*((26411/100000 : ℝ)+(1891/100000 : ℝ)))^(2183/512 : ℝ) := by
    rw [show (122584831597368814317/122600000000000000000 : ℝ)+(8022731662693/2452000000000000 : ℝ)*((26411/100000 : ℝ)+(1891/100000 : ℝ))=(2502005735585799/2500000000000000 : ℝ) by norm_num, show 1+(1712577804659493/500000000000000000 : ℝ)+(898272564111/20000000000000000000 : ℝ)=(20068504010458943831/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1712577804659493/500000000000000000 : ℝ) ≤ ((122584831597368814317/122600000000000000000 : ℝ)+2*(8022731662693/2452000000000000 : ℝ)*(26411/100000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (122584831597368814317/122600000000000000000 : ℝ)+2*(8022731662693/2452000000000000 : ℝ)*(26411/100000 : ℝ)=(10016045674005889/10000000000000000 : ℝ) by norm_num, show 1+2*(1712577804659493/500000000000000000 : ℝ)=(251712577804659493/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (122584831597368814317/122600000000000000000 : ℝ)*(X 1 0+X 2 0)+(8022731662693/2452000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1891/100000 : ℝ)) (hi := (26411/100000 : ℝ)) (c := (122584831597368814317/122600000000000000000 : ℝ)) (alpha := (8022731662693/2452000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (122584831597368814317/122600000000000000000 : ℝ)*(X 0 1+X 2 1)+(8022731662693/2452000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1891/100000 : ℝ)) (hi := (26411/100000 : ℝ)) (c := (122584831597368814317/122600000000000000000 : ℝ)) (alpha := (8022731662693/2452000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (122584831597368814317/122600000000000000000 : ℝ)*(X 0 2+X 1 2)+(8022731662693/2452000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1891/100000 : ℝ)) (hi := (26411/100000 : ℝ)) (c := (122584831597368814317/122600000000000000000 : ℝ)) (alpha := (8022731662693/2452000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-973409571/5000000000 : ℝ)*X 0 0+(5614174413/10000000000 : ℝ)*X 0 1+(2534427529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5399030761/10000000000 : ℝ)*X 1 0+(-559067307/2500000000 : ℝ)*X 1 1+(2534427849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1079806263/2000000000 : ℝ)*X 2 0+(5068855327/10000000000 : ℝ)*X 2 1+(-111813449/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140314173/5000000000 : ℝ)*X 0 0+(3731557561/10000000000 : ℝ)*X 0 1+(4901762403/10000000000 : ℝ)*X 0 2+(2140314173/5000000000 : ℝ)*X 1 0+(3731557561/10000000000 : ℝ)*X 1 1+(4901762403/10000000000 : ℝ)*X 1 2+(2140314173/5000000000 : ℝ)*X 2 0+(3731557561/10000000000 : ℝ)*X 2 1+(4901762403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-486812089/2500000000 : ℝ)*X 0 0+(5075360727/10000000000 : ℝ)*X 0 1+(1121511293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256789291/10000000000 : ℝ)*X 1 0+(-1697568511/10000000000 : ℝ)*X 1 1+(1401889083/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256789897/10000000000 : ℝ)*X 2 0+(2803778407/5000000000 : ℝ)*X 2 1+(-21219587/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2140775457/5000000000 : ℝ)*X 0 0+(4887800673/10000000000 : ℝ)*X 0 1+(374575883/1000000000 : ℝ)*X 0 2+(2140775457/5000000000 : ℝ)*X 1 0+(4887800673/10000000000 : ℝ)*X 1 1+(374575883/1000000000 : ℝ)*X 1 2+(2140775457/5000000000 : ℝ)*X 2 0+(4887800673/10000000000 : ℝ)*X 2 1+(374575883/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198018104645231815201821/122600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51953901/20000000000000 : ℝ)*(base19) + (110933167/25000000000000 : ℝ)*(base23) + (4448577/50000000000000 : ℝ)*(upper4) + (16701173/20000000000000 : ℝ)*(upper5) + (1344175335966899/100000000000000 : ℝ)*(major0) + (1344175335966899/100000000000000 : ℝ)*(major1) + (1344175335966899/100000000000000 : ℝ)*(major2) + (229223895250429/12500000000000 : ℝ)*(sp0) + (1833795458728631/100000000000000 : ℝ)*(sp1) + (57306116896053/3125000000000 : ℝ)*(sp2) + (213638228252573/25000000000000 : ℝ)*(sp3) + (1255600733/25000000000000 : ℝ)*(sp4) + (116477057/25000000000000 : ℝ)*(sp5) + (1520678611/100000000000000 : ℝ)*(sp7) + (854554433688903/100000000000000 : ℝ)*(f.failure) + (458449046101591/25000000000000 : ℝ)*(f.sum) + (694196142910993/122600000000000000000000000000 : ℝ)*base66 + (91206555101639642983/12260000000000000000000000000000000 : ℝ)*base67 + (37516444413419642983/12260000000000000000000000000000000 : ℝ)*base69 + (62912458586160357017/12260000000000000000000000000000000 : ℝ)*base72 + (248464800657607/122600000000000000000000000000 : ℝ)*base73 + (14640963384060357017/12260000000000000000000000000000000 : ℝ)*base76 + (9473395280420357017/12260000000000000000000000000000000 : ℝ)*base78 + (60025186938519642983/12260000000000000000000000000000000 : ℝ)*base79 + (80941671408593/122600000000000000000000000000 : ℝ)*base82 + (27969283/10000000000000000000000 : ℝ)*base89 + (27969283/10000000000000000000000 : ℝ)*base91 + (27969283/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144453438798854529160136091/30650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230152057/100000000000000 : ℝ)*(base1) + (1259614509/100000000000000 : ℝ)*(base19) + (199338289/12500000000000 : ℝ)*(base23) + (17757447/20000000000000 : ℝ)*(upper3) + (122063803/50000000000000 : ℝ)*(upper5) + (6886588080141/500000000000 : ℝ)*(major0) + (6886588080141/500000000000 : ℝ)*(major1) + (6886588080141/500000000000 : ℝ)*(major2) + (576278209/10000000000000 : ℝ)*(sp1) + (405657983/4000000000000 : ℝ)*(sp2) + (1879010791043053/100000000000000 : ℝ)*(sp4) + (1879003538494397/100000000000000 : ℝ)*(sp5) + (1878998824735109/100000000000000 : ℝ)*(sp6) + (175124856782671/20000000000000 : ℝ)*(sp7) + (218906128516353/25000000000000 : ℝ)*(f.failure) + (469752640222749/25000000000000 : ℝ)*(f.sum) + (1039583905687/613000000000000000000000000 : ℝ)*base65 + (265716975909971303/61300000000000000000000000000000 : ℝ)*base68 + (81455889846328697/61300000000000000000000000000000 : ℝ)*base69 + (143942199023271303/61300000000000000000000000000000 : ℝ)*base72 + (978070607951/613000000000000000000000000 : ℝ)*base74 + (147093908233628697/61300000000000000000000000000000 : ℝ)*base75 + (410466132328571303/61300000000000000000000000000000 : ℝ)*base78 + (228706440095971303/61300000000000000000000000000000 : ℝ)*base80 + (21829828917/613000000000000000000000000 : ℝ)*base82 + (8826267/2500000000000000000000 : ℝ)*base90 + (8826267/2500000000000000000000 : ℝ)*base92 + (8826267/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1407_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26411/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1867/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3799/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1407_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1407_s2_0 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-495406287/2500000000 : ℝ)*x 0 + (5463227249/10000000000 : ℝ)*x 1 + (1039485119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495406287/2500000000 : ℝ)^4367 ≤ (12069546992241/100000000000000 : ℝ)^3343 := by
    have hnat : (495406287 : ℕ)^4367*100000000000000^3343 ≤ 12069546992241^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495406287 2500000000 12069546992241 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463227249/10000000000 : ℝ)^4367 ≤ (72635158377/160000000000 : ℝ)^3343 := by
    have hnat : (5463227249 : ℕ)^4367*160000000000^3343 ≤ 72635158377^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463227249 10000000000 72635158377 160000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039485119/2000000000 : ℝ)^4367 ≤ (21266739501321/50000000000000 : ℝ)^3343 := by
    have hnat : (1039485119 : ℕ)^4367*50000000000000^3343 ≤ 21266739501321^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039485119 2000000000 21266739501321 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-495406287/2500000000 : ℝ), (5463227249/10000000000 : ℝ), (1039485119/2000000000 : ℝ)] ![(12069546992241/100000000000000 : ℝ), (72635158377/160000000000 : ℝ), (21266739501321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-495406287/2500000000 : ℝ)|^4367 ≤ (12069546992241/100000000000000 : ℝ)^3343
        have hw : |(-495406287/2500000000 : ℝ)|=(495406287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463227249/10000000000 : ℝ)|^4367 ≤ (72635158377/160000000000 : ℝ)^3343
        have hw : |(5463227249/10000000000 : ℝ)|=(5463227249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039485119/2000000000 : ℝ)|^4367 ≤ (21266739501321/50000000000000 : ℝ)^3343
        have hw : |(1039485119/2000000000 : ℝ)|=(1039485119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_1 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361553471/10000000000 : ℝ)*x 0 + (-2118515259/10000000000 : ℝ)*x 1 + (5197425579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361553471/10000000000 : ℝ)^4367 ≤ (44296478193099/100000000000000 : ℝ)^3343 := by
    have hnat : (5361553471 : ℕ)^4367*100000000000000^3343 ≤ 44296478193099^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361553471 10000000000 44296478193099 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118515259/10000000000 : ℝ)^4367 ≤ (6585021480357/50000000000000 : ℝ)^3343 := by
    have hnat : (2118515259 : ℕ)^4367*50000000000000^3343 ≤ 6585021480357^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118515259 10000000000 6585021480357 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5197425579/10000000000 : ℝ)^4367 ≤ (21266739415799/50000000000000 : ℝ)^3343 := by
    have hnat : (5197425579 : ℕ)^4367*50000000000000^3343 ≤ 21266739415799^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197425579 10000000000 21266739415799 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361553471/10000000000 : ℝ), (-2118515259/10000000000 : ℝ), (5197425579/10000000000 : ℝ)] ![(44296478193099/100000000000000 : ℝ), (6585021480357/50000000000000 : ℝ), (21266739415799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361553471/10000000000 : ℝ)|^4367 ≤ (44296478193099/100000000000000 : ℝ)^3343
        have hw : |(5361553471/10000000000 : ℝ)|=(5361553471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2118515259/10000000000 : ℝ)|^4367 ≤ (6585021480357/50000000000000 : ℝ)^3343
        have hw : |(-2118515259/10000000000 : ℝ)|=(2118515259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5197425579/10000000000 : ℝ)|^4367 ≤ (21266739415799/50000000000000 : ℝ)^3343
        have hw : |(5197425579/10000000000 : ℝ)|=(5197425579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_2 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680776621/5000000000 : ℝ)*x 0 + (2598712919/5000000000 : ℝ)*x 1 + (-1059257611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680776621/5000000000 : ℝ)^4367 ≤ (22148237860799/50000000000000 : ℝ)^3343 := by
    have hnat : (2680776621 : ℕ)^4367*50000000000000^3343 ≤ 22148237860799^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680776621 5000000000 22148237860799 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598712919/5000000000 : ℝ)^4367 ≤ (42533481600383/100000000000000 : ℝ)^3343 := by
    have hnat : (2598712919 : ℕ)^4367*100000000000000^3343 ≤ 42533481600383^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598712919 5000000000 42533481600383 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059257611/5000000000 : ℝ)^4367 ≤ (13170042660241/100000000000000 : ℝ)^3343 := by
    have hnat : (1059257611 : ℕ)^4367*100000000000000^3343 ≤ 13170042660241^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059257611 5000000000 13170042660241 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680776621/5000000000 : ℝ), (2598712919/5000000000 : ℝ), (-1059257611/5000000000 : ℝ)] ![(22148237860799/50000000000000 : ℝ), (42533481600383/100000000000000 : ℝ), (13170042660241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680776621/5000000000 : ℝ)|^4367 ≤ (22148237860799/50000000000000 : ℝ)^3343
        have hw : |(2680776621/5000000000 : ℝ)|=(2680776621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598712919/5000000000 : ℝ)|^4367 ≤ (42533481600383/100000000000000 : ℝ)^3343
        have hw : |(2598712919/5000000000 : ℝ)|=(2598712919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059257611/5000000000 : ℝ)|^4367 ≤ (13170042660241/100000000000000 : ℝ)^3343
        have hw : |(-1059257611/5000000000 : ℝ)|=(1059257611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_3 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152571507/5000000000 : ℝ)*x 0 + (4028509991/10000000000 : ℝ)*x 1 + (4598896217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152571507/5000000000 : ℝ)^4367 ≤ (33256282353011/100000000000000 : ℝ)^3343 := by
    have hnat : (2152571507 : ℕ)^4367*100000000000000^3343 ≤ 33256282353011^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152571507 5000000000 33256282353011 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028509991/10000000000 : ℝ)^4367 ≤ (30492678185889/100000000000000 : ℝ)^3343 := by
    have hnat : (4028509991 : ℕ)^4367*100000000000000^3343 ≤ 30492678185889^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028509991 10000000000 30492678185889 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4598896217/10000000000 : ℝ)^4367 ≤ (36251039441049/100000000000000 : ℝ)^3343 := by
    have hnat : (4598896217 : ℕ)^4367*100000000000000^3343 ≤ 36251039441049^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4598896217 10000000000 36251039441049 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152571507/5000000000 : ℝ), (4028509991/10000000000 : ℝ), (4598896217/10000000000 : ℝ)] ![(33256282353011/100000000000000 : ℝ), (30492678185889/100000000000000 : ℝ), (36251039441049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152571507/5000000000 : ℝ)|^4367 ≤ (33256282353011/100000000000000 : ℝ)^3343
        have hw : |(2152571507/5000000000 : ℝ)|=(2152571507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028509991/10000000000 : ℝ)|^4367 ≤ (30492678185889/100000000000000 : ℝ)^3343
        have hw : |(4028509991/10000000000 : ℝ)|=(4028509991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4598896217/10000000000 : ℝ)|^4367 ≤ (36251039441049/100000000000000 : ℝ)^3343
        have hw : |(4598896217/10000000000 : ℝ)|=(4598896217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_4 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-990837341/5000000000 : ℝ)*x 0 + (1299745189/2500000000 : ℝ)*x 1 + (5461659221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990837341/5000000000 : ℝ)^4367 ≤ (12069941105769/100000000000000 : ℝ)^3343 := by
    have hnat : (990837341 : ℕ)^4367*100000000000000^3343 ≤ 12069941105769^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990837341 5000000000 12069941105769 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1299745189/2500000000 : ℝ)^4367 ≤ (42550104884829/100000000000000 : ℝ)^3343 := by
    have hnat : (1299745189 : ℕ)^4367*100000000000000^3343 ≤ 42550104884829^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299745189 2500000000 42550104884829 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461659221/10000000000 : ℝ)^4367 ≤ (11344988500129/25000000000000 : ℝ)^3343 := by
    have hnat : (5461659221 : ℕ)^4367*25000000000000^3343 ≤ 11344988500129^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461659221 10000000000 11344988500129 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990837341/5000000000 : ℝ), (1299745189/2500000000 : ℝ), (5461659221/10000000000 : ℝ)] ![(12069941105769/100000000000000 : ℝ), (42550104884829/100000000000000 : ℝ), (11344988500129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990837341/5000000000 : ℝ)|^4367 ≤ (12069941105769/100000000000000 : ℝ)^3343
        have hw : |(-990837341/5000000000 : ℝ)|=(990837341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1299745189/2500000000 : ℝ)|^4367 ≤ (42550104884829/100000000000000 : ℝ)^3343
        have hw : |(1299745189/2500000000 : ℝ)|=(1299745189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461659221/10000000000 : ℝ)|^4367 ≤ (11344988500129/25000000000000 : ℝ)^3343
        have hw : |(5461659221/10000000000 : ℝ)|=(5461659221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_5 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292581939/10000000000 : ℝ)*x 0 + (-1854282229/10000000000 : ℝ)*x 1 + (273082947/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292581939/10000000000 : ℝ)^4367 ≤ (1742142729031/4000000000000 : ℝ)^3343 := by
    have hnat : (5292581939 : ℕ)^4367*4000000000000^3343 ≤ 1742142729031^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292581939 10000000000 1742142729031 4000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1854282229/10000000000 : ℝ)^4367 ≤ (11066480810889/100000000000000 : ℝ)^3343 := by
    have hnat : (1854282229 : ℕ)^4367*100000000000000^3343 ≤ 11066480810889^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854282229 10000000000 11066480810889 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273082947/500000000 : ℝ)^4367 ≤ (45379950950567/100000000000000 : ℝ)^3343 := by
    have hnat : (273082947 : ℕ)^4367*100000000000000^3343 ≤ 45379950950567^3343*500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273082947 500000000 45379950950567 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292581939/10000000000 : ℝ), (-1854282229/10000000000 : ℝ), (273082947/500000000 : ℝ)] ![(1742142729031/4000000000000 : ℝ), (11066480810889/100000000000000 : ℝ), (45379950950567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292581939/10000000000 : ℝ)|^4367 ≤ (1742142729031/4000000000000 : ℝ)^3343
        have hw : |(5292581939/10000000000 : ℝ)|=(5292581939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1854282229/10000000000 : ℝ)|^4367 ≤ (11066480810889/100000000000000 : ℝ)^3343
        have hw : |(-1854282229/10000000000 : ℝ)|=(1854282229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(273082947/500000000 : ℝ)|^4367 ≤ (45379950950567/100000000000000 : ℝ)^3343
        have hw : |(273082947/500000000 : ℝ)|=(273082947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_6 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323145841/2500000000 : ℝ)*x 0 + (1092331783/2000000000 : ℝ)*x 1 + (-1854280299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323145841/2500000000 : ℝ)^4367 ≤ (10888395886083/25000000000000 : ℝ)^3343 := by
    have hnat : (1323145841 : ℕ)^4367*25000000000000^3343 ≤ 10888395886083^3343*2500000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323145841 2500000000 10888395886083 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092331783/2000000000 : ℝ)^4367 ≤ (45379950679219/100000000000000 : ℝ)^3343 := by
    have hnat : (1092331783 : ℕ)^4367*100000000000000^3343 ≤ 45379950679219^3343*2000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092331783 2000000000 45379950679219 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1854280299/10000000000 : ℝ)^4367 ≤ (1106646576431/10000000000000 : ℝ)^3343 := by
    have hnat : (1854280299 : ℕ)^4367*10000000000000^3343 ≤ 1106646576431^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854280299 10000000000 1106646576431 10000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323145841/2500000000 : ℝ), (1092331783/2000000000 : ℝ), (-1854280299/10000000000 : ℝ)] ![(10888395886083/25000000000000 : ℝ), (45379950679219/100000000000000 : ℝ), (1106646576431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323145841/2500000000 : ℝ)|^4367 ≤ (10888395886083/25000000000000 : ℝ)^3343
        have hw : |(1323145841/2500000000 : ℝ)|=(1323145841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092331783/2000000000 : ℝ)|^4367 ≤ (45379950679219/100000000000000 : ℝ)^3343
        have hw : |(1092331783/2000000000 : ℝ)|=(1092331783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1854280299/10000000000 : ℝ)|^4367 ≤ (1106646576431/10000000000000 : ℝ)^3343
        have hw : |(-1854280299/10000000000 : ℝ)|=(1854280299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1407_s2_7 (p : ℝ) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2152625257/5000000000 : ℝ)*x 0 + (4595559447/10000000000 : ℝ)*x 1 + (4031874363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152625257/5000000000 : ℝ)^4367 ≤ (16628683568237/50000000000000 : ℝ)^3343 := by
    have hnat : (2152625257 : ℕ)^4367*50000000000000^3343 ≤ 16628683568237^3343*5000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152625257 5000000000 16628683568237 50000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4595559447/10000000000 : ℝ)^4367 ≤ (36216684305119/100000000000000 : ℝ)^3343 := by
    have hnat : (4595559447 : ℕ)^4367*100000000000000^3343 ≤ 36216684305119^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595559447 10000000000 36216684305119 100000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031874363/10000000000 : ℝ)^4367 ≤ (7631487136189/25000000000000 : ℝ)^3343 := by
    have hnat : (4031874363 : ℕ)^4367*25000000000000^3343 ≤ 7631487136189^3343*10000000000^4367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031874363 10000000000 7631487136189 25000000000000 4367 3343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4367/1024 : ℝ)) 4367 3343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152625257/5000000000 : ℝ), (4595559447/10000000000 : ℝ), (4031874363/10000000000 : ℝ)] ![(16628683568237/50000000000000 : ℝ), (36216684305119/100000000000000 : ℝ), (7631487136189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152625257/5000000000 : ℝ)|^4367 ≤ (16628683568237/50000000000000 : ℝ)^3343
        have hw : |(2152625257/5000000000 : ℝ)|=(2152625257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4595559447/10000000000 : ℝ)|^4367 ≤ (36216684305119/100000000000000 : ℝ)^3343
        have hw : |(4595559447/10000000000 : ℝ)|=(4595559447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031874363/10000000000 : ℝ)|^4367 ≤ (7631487136189/25000000000000 : ℝ)^3343
        have hw : |(4031874363/10000000000 : ℝ)|=(4031874363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1407_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10247/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15869/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1867/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1867/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1867/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1867/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1867/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1867/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1867/25000 : ℝ) ^ (2183/512 : ℝ) ≤ (1569325040830343/100000000000000000000 : ℝ) := by
    have hpowers : (1867/25000 : ℝ)^2183 ≤ (1569325040830343/100000000000000000000 : ℝ)^512 := by
      have hnat : (1867 : ℕ)^2183*100000000000000000000^512 ≤ 1569325040830343^512*25000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1867 25000 1569325040830343 100000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1867/25000 : ℝ)) (X := (1569325040830343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3799/20000 : ℝ) ^ (2183/512 : ℝ) ≤ (42007290198500939/50000000000000000000 : ℝ) := by
    have hpowers : (3799/20000 : ℝ)^2183 ≤ (42007290198500939/50000000000000000000 : ℝ)^512 := by
      have hnat : (3799 : ℕ)^2183*50000000000000000000^512 ≤ 42007290198500939^512*20000^2183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3799 20000 42007290198500939 50000000000000000000 2183 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3799/20000 : ℝ)) (X := (42007290198500939/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001569325040830343/50000000000000000000 : ℝ) ≤ (2000014722579369/2000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (50001569325040830343/50000000000000000000 : ℝ)^512 ≤ (2000014722579369/2000000000000000 : ℝ)^2183 := by
      have hnat : (50001569325040830343 : ℕ)^512*2000000000000000^2183 ≤ 2000014722579369^2183*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001569325040830343 50000000000000000000 2000014722579369 2000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000014722579369/2000000000000000 : ℝ)) (X := (50001569325040830343/50000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100085583905437832221/100000000000000000000 : ℝ) ≤ (10002006624538259/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (100085583905437832221/100000000000000000000 : ℝ)^512 ≤ (10002006624538259/10000000000000000 : ℝ)^2183 := by
      have hnat : (100085583905437832221 : ℕ)^512*10000000000000000^2183 ≤ 10002006624538259^2183*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100085583905437832221 100000000000000000000 10002006624538259 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002006624538259/10000000000000000 : ℝ)) (X := (100085583905437832221/100000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25042007290198500939/25000000000000000000 : ℝ) ≤ (10003939636179673/10000000000000000 : ℝ) ^ (2183/512 : ℝ) := by
    have hpowers : (25042007290198500939/25000000000000000000 : ℝ)^512 ≤ (10003939636179673/10000000000000000 : ℝ)^2183 := by
      have hnat : (25042007290198500939 : ℕ)^512*10000000000000000^2183 ≤ 10003939636179673^2183*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25042007290198500939 25000000000000000000 10003939636179673 10000000000000000 512 2183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003939636179673/10000000000000000 : ℝ)) (X := (25042007290198500939/25000000000000000000 : ℝ)) (by norm_num) 2183 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1569325040830343/100000000000000000000 : ℝ) ≤ ((115241977073985772811/115270000000000000000 : ℝ)+2*(966505820707/576350000000000 : ℝ)*(1867/25000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (115241977073985772811/115270000000000000000 : ℝ)+2*(966505820707/576350000000000 : ℝ)*(1867/25000 : ℝ)=(2000014722579369/2000000000000000 : ℝ) by norm_num, show 1+2*(1569325040830343/100000000000000000000 : ℝ)=(50001569325040830343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42007290198500939/50000000000000000000 : ℝ)+(1569325040830343/100000000000000000000 : ℝ) ≤ ((115241977073985772811/115270000000000000000 : ℝ)+(966505820707/576350000000000 : ℝ)*((3799/20000 : ℝ)+(1867/25000 : ℝ)))^(2183/512 : ℝ) := by
    rw [show (115241977073985772811/115270000000000000000 : ℝ)+(966505820707/576350000000000 : ℝ)*((3799/20000 : ℝ)+(1867/25000 : ℝ))=(10002006624538259/10000000000000000 : ℝ) by norm_num, show 1+(42007290198500939/50000000000000000000 : ℝ)+(1569325040830343/100000000000000000000 : ℝ)=(100085583905437832221/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42007290198500939/50000000000000000000 : ℝ) ≤ ((115241977073985772811/115270000000000000000 : ℝ)+2*(966505820707/576350000000000 : ℝ)*(3799/20000 : ℝ))^(2183/512 : ℝ) := by
    rw [show (115241977073985772811/115270000000000000000 : ℝ)+2*(966505820707/576350000000000 : ℝ)*(3799/20000 : ℝ)=(10003939636179673/10000000000000000 : ℝ) by norm_num, show 1+2*(42007290198500939/50000000000000000000 : ℝ)=(25042007290198500939/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (115241977073985772811/115270000000000000000 : ℝ)*(X 1 0+X 2 0)+(966505820707/576350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1867/25000 : ℝ)) (hi := (3799/20000 : ℝ)) (c := (115241977073985772811/115270000000000000000 : ℝ)) (alpha := (966505820707/576350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (115241977073985772811/115270000000000000000 : ℝ)*(X 0 1+X 2 1)+(966505820707/576350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1867/25000 : ℝ)) (hi := (3799/20000 : ℝ)) (c := (115241977073985772811/115270000000000000000 : ℝ)) (alpha := (966505820707/576350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (115241977073985772811/115270000000000000000 : ℝ)*(X 0 2+X 1 2)+(966505820707/576350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2183/512 : ℝ)) (lo := (1867/25000 : ℝ)) (hi := (3799/20000 : ℝ)) (c := (115241977073985772811/115270000000000000000 : ℝ)) (alpha := (966505820707/576350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-495406287/2500000000 : ℝ)*X 0 0+(5463227249/10000000000 : ℝ)*X 0 1+(1039485119/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361553471/10000000000 : ℝ)*X 1 0+(-2118515259/10000000000 : ℝ)*X 1 1+(5197425579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680776621/5000000000 : ℝ)*X 2 0+(2598712919/5000000000 : ℝ)*X 2 1+(-1059257611/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152571507/5000000000 : ℝ)*X 0 0+(4028509991/10000000000 : ℝ)*X 0 1+(4598896217/10000000000 : ℝ)*X 0 2+(2152571507/5000000000 : ℝ)*X 1 0+(4028509991/10000000000 : ℝ)*X 1 1+(4598896217/10000000000 : ℝ)*X 1 2+(2152571507/5000000000 : ℝ)*X 2 0+(4028509991/10000000000 : ℝ)*X 2 1+(4598896217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-990837341/5000000000 : ℝ)*X 0 0+(1299745189/2500000000 : ℝ)*X 0 1+(5461659221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292581939/10000000000 : ℝ)*X 1 0+(-1854282229/10000000000 : ℝ)*X 1 1+(273082947/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323145841/2500000000 : ℝ)*X 2 0+(1092331783/2000000000 : ℝ)*X 2 1+(-1854280299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152625257/5000000000 : ℝ)*X 0 0+(4595559447/10000000000 : ℝ)*X 0 1+(4031874363/10000000000 : ℝ)*X 0 2+(2152625257/5000000000 : ℝ)*X 1 0+(4595559447/10000000000 : ℝ)*X 1 1+(4031874363/10000000000 : ℝ)*X 1 2+(2152625257/5000000000 : ℝ)*X 2 0+(4595559447/10000000000 : ℝ)*X 2 1+(4031874363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1407_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8445329584381377957102703017/1440875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (845509837/100000000000000 : ℝ)*(base19) + (531157029/100000000000000 : ℝ)*(base23) + (20596761/25000000000000 : ℝ)*(lower2) + (179106033/100000000000000 : ℝ)*(upper3) + (1737273/3125000000000 : ℝ)*(upper5) + (1378857595055649/50000000000000 : ℝ)*(major0) + (1378857595055649/50000000000000 : ℝ)*(major1) + (1378857595055649/50000000000000 : ℝ)*(major2) + (188110736175201/5000000000000 : ℝ)*(sp0) + (1881111119706509/50000000000000 : ℝ)*(sp1) + (1881111276882913/50000000000000 : ℝ)*(sp2) + (876600953345901/50000000000000 : ℝ)*(sp3) + (1672283767/20000000000000 : ℝ)*(sp4) + (1038646581/20000000000000 : ℝ)*(sp7) + (876603549962353/50000000000000 : ℝ)*(f.failure) + (752444616984571/20000000000000 : ℝ)*(f.sum) + (8510216099923/14408750000000000000000000000 : ℝ)*base65 + (83777284011184740661/5763500000000000000000000000000000 : ℝ)*base68 + (35375234803699240661/5763500000000000000000000000000000 : ℝ)*base70 + (81957990966741240661/5763500000000000000000000000000000 : ℝ)*base72 + (25582830919447/57635000000000000000000000000 : ℝ)*base73 + (31021302396773740661/5763500000000000000000000000000000 : ℝ)*base76 + (10035408750169759339/5763500000000000000000000000000000 : ℝ)*base77 + (80364323443482740661/5763500000000000000000000000000000 : ℝ)*base80 + (92827399653977/57635000000000000000000000000 : ℝ)*base81 + (52220267/5000000000000000000000 : ℝ)*base90 + (52220267/5000000000000000000000 : ℝ)*base92 + (52220267/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (185821823389951741369743171/72043750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400684923/100000000000000 : ℝ)*(base19) + (109865387/6250000000000 : ℝ)*(base23) + (78819803/50000000000000 : ℝ)*(lower2) + (74869437/100000000000000 : ℝ)*(upper3) + (117255337/100000000000000 : ℝ)*(lower4) + (69762338762837/2500000000000 : ℝ)*(major0) + (69762338762837/2500000000000 : ℝ)*(major1) + (69762338762837/2500000000000 : ℝ)*(major2) + (7836178919/25000000000000 : ℝ)*(sp2) + (737732987/100000000000000 : ℝ)*(sp3) + (761388239061833/20000000000000 : ℝ)*(sp4) + (1903470397312121/50000000000000 : ℝ)*(sp5) + (118965877898353/3125000000000 : ℝ)*(sp6) + (1774045082008423/100000000000000 : ℝ)*(sp7) + (177404581974141/10000000000000 : ℝ)*(f.failure) + (761388239061833/20000000000000 : ℝ)*(f.sum) + (36291167800487/5763500000000000000000000000 : ℝ)*base65 + (2432672135589525193/288175000000000000000000000000000 : ℝ)*base68 + (2316856405624150193/288175000000000000000000000000000 : ℝ)*base70 + (1452451656729025193/288175000000000000000000000000000 : ℝ)*base72 + (3196857147021/2881750000000000000000000000 : ℝ)*base73 + (95592847471775193/288175000000000000000000000000000 : ℝ)*base76 + (1046367001970175193/288175000000000000000000000000000 : ℝ)*base78 + (754211505538574807/288175000000000000000000000000000 : ℝ)*base79 + (1262403211399/288175000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1325999/1000000000000000000000 : ℝ)*base90 + (1325999/1000000000000000000000 : ℝ)*base92 + (1325999/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1407_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1867/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15869/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1407_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1407_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15869/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1407_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1407_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1407_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2183/512 : ℝ) ≤ p) (hpb : p ≤ (4367/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157295461/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15869/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1407_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
