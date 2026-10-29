-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1624_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:02.177253+00:00
-- url     : https://prove2.me/submissions/d578aeb6-d983-49af-b903-62ead63ff99a

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
theorem support_rectangle_w1624_s3_0 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1669592511/10000000000 : ℝ)*x 0 + (1363889537/2500000000 : ℝ)*x 1 + (1295437933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669592511/10000000000 : ℝ)^4815 ≤ (10295018780037/100000000000000 : ℝ)^3791 := by
    have hnat : (1669592511 : ℕ)^4815*100000000000000^3791 ≤ 10295018780037^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669592511 10000000000 10295018780037 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1363889537/2500000000 : ℝ)^4815 ≤ (23159326476883/50000000000000 : ℝ)^3791 := by
    have hnat : (1363889537 : ℕ)^4815*50000000000000^3791 ≤ 23159326476883^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363889537 2500000000 23159326476883 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295437933/2500000000 : ℝ)^4815 ≤ (10846582061261/25000000000000 : ℝ)^3791 := by
    have hnat : (1295437933 : ℕ)^4815*25000000000000^3791 ≤ 10846582061261^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295437933 2500000000 10846582061261 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1669592511/10000000000 : ℝ), (1363889537/2500000000 : ℝ), (1295437933/2500000000 : ℝ)] ![(10295018780037/100000000000000 : ℝ), (23159326476883/50000000000000 : ℝ), (10846582061261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1669592511/10000000000 : ℝ)|^4815 ≤ (10295018780037/100000000000000 : ℝ)^3791
        have hw : |(-1669592511/10000000000 : ℝ)|=(1669592511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1363889537/2500000000 : ℝ)|^4815 ≤ (23159326476883/50000000000000 : ℝ)^3791
        have hw : |(1363889537/2500000000 : ℝ)|=(1363889537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295437933/2500000000 : ℝ)|^4815 ≤ (10846582061261/25000000000000 : ℝ)^3791
        have hw : |(1295437933/2500000000 : ℝ)|=(1295437933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_1 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351657491/10000000000 : ℝ)*x 0 + (-1810704061/10000000000 : ℝ)*x 1 + (5181751743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351657491/10000000000 : ℝ)^4815 ≤ (45201136843193/100000000000000 : ℝ)^3791 := by
    have hnat : (5351657491 : ℕ)^4815*100000000000000^3791 ≤ 45201136843193^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351657491 10000000000 45201136843193 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1810704061/10000000000 : ℝ)^4815 ≤ (2282506956917/20000000000000 : ℝ)^3791 := by
    have hnat : (1810704061 : ℕ)^4815*20000000000000^3791 ≤ 2282506956917^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810704061 10000000000 2282506956917 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181751743/10000000000 : ℝ)^4815 ≤ (5423291045253/12500000000000 : ℝ)^3791 := by
    have hnat : (5181751743 : ℕ)^4815*12500000000000^3791 ≤ 5423291045253^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181751743 10000000000 5423291045253 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351657491/10000000000 : ℝ), (-1810704061/10000000000 : ℝ), (5181751743/10000000000 : ℝ)] ![(45201136843193/100000000000000 : ℝ), (2282506956917/20000000000000 : ℝ), (5423291045253/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351657491/10000000000 : ℝ)|^4815 ≤ (45201136843193/100000000000000 : ℝ)^3791
        have hw : |(5351657491/10000000000 : ℝ)|=(5351657491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1810704061/10000000000 : ℝ)|^4815 ≤ (2282506956917/20000000000000 : ℝ)^3791
        have hw : |(-1810704061/10000000000 : ℝ)|=(1810704061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181751743/10000000000 : ℝ)|^4815 ≤ (5423291045253/12500000000000 : ℝ)^3791
        have hw : |(5181751743/10000000000 : ℝ)|=(5181751743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_2 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140663/4000000 : ℝ)*x 0 + (2590875877/5000000000 : ℝ)*x 1 + (-905352017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140663/4000000 : ℝ)^4815 ≤ (45201136939741/100000000000000 : ℝ)^3791 := by
    have hnat : (2140663 : ℕ)^4815*100000000000000^3791 ≤ 45201136939741^3791*4000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140663 4000000 45201136939741 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590875877/5000000000 : ℝ)^4815 ≤ (10846582119751/25000000000000 : ℝ)^3791 := by
    have hnat : (2590875877 : ℕ)^4815*25000000000000^3791 ≤ 10846582119751^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590875877 5000000000 10846582119751 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905352017/5000000000 : ℝ)^4815 ≤ (5706267284221/50000000000000 : ℝ)^3791 := by
    have hnat : (905352017 : ℕ)^4815*50000000000000^3791 ≤ 5706267284221^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905352017 5000000000 5706267284221 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140663/4000000 : ℝ), (2590875877/5000000000 : ℝ), (-905352017/5000000000 : ℝ)] ![(45201136939741/100000000000000 : ℝ), (10846582119751/25000000000000 : ℝ), (5706267284221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140663/4000000 : ℝ)|^4815 ≤ (45201136939741/100000000000000 : ℝ)^3791
        have hw : |(2140663/4000000 : ℝ)|=(2140663/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590875877/5000000000 : ℝ)|^4815 ≤ (10846582119751/25000000000000 : ℝ)^3791
        have hw : |(2590875877/5000000000 : ℝ)|=(2590875877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-905352017/5000000000 : ℝ)|^4815 ≤ (5706267284221/50000000000000 : ℝ)^3791
        have hw : |(-905352017/5000000000 : ℝ)|=(905352017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_3 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050275069/2500000000 : ℝ)*x 0 + (1934502297/5000000000 : ℝ)*x 1 + (4554260221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050275069/2500000000 : ℝ)^4815 ≤ (6647499996629/20000000000000 : ℝ)^3791 := by
    have hnat : (1050275069 : ℕ)^4815*20000000000000^3791 ≤ 6647499996629^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050275069 2500000000 6647499996629 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934502297/5000000000 : ℝ)^4815 ≤ (3742090422923/12500000000000 : ℝ)^3791 := by
    have hnat : (1934502297 : ℕ)^4815*12500000000000^3791 ≤ 3742090422923^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934502297 5000000000 3742090422923 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554260221/10000000000 : ℝ)^4815 ≤ (7365155323749/20000000000000 : ℝ)^3791 := by
    have hnat : (4554260221 : ℕ)^4815*20000000000000^3791 ≤ 7365155323749^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554260221 10000000000 7365155323749 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050275069/2500000000 : ℝ), (1934502297/5000000000 : ℝ), (4554260221/10000000000 : ℝ)] ![(6647499996629/20000000000000 : ℝ), (3742090422923/12500000000000 : ℝ), (7365155323749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050275069/2500000000 : ℝ)|^4815 ≤ (6647499996629/20000000000000 : ℝ)^3791
        have hw : |(1050275069/2500000000 : ℝ)|=(1050275069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1934502297/5000000000 : ℝ)|^4815 ≤ (3742090422923/12500000000000 : ℝ)^3791
        have hw : |(1934502297/5000000000 : ℝ)|=(1934502297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554260221/10000000000 : ℝ)|^4815 ≤ (7365155323749/20000000000000 : ℝ)^3791
        have hw : |(4554260221/10000000000 : ℝ)|=(4554260221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_4 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1669661081/10000000000 : ℝ)*x 0 + (1295951077/2500000000 : ℝ)*x 1 + (1363370977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669661081/10000000000 : ℝ)^4815 ≤ (5147777903271/50000000000000 : ℝ)^3791 := by
    have hnat : (1669661081 : ℕ)^4815*50000000000000^3791 ≤ 5147777903271^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669661081 10000000000 5147777903271 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295951077/2500000000 : ℝ)^4815 ≤ (5426019702377/12500000000000 : ℝ)^3791 := by
    have hnat : (1295951077 : ℕ)^4815*12500000000000^3791 ≤ 5426019702377^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295951077 2500000000 5426019702377 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363370977/2500000000 : ℝ)^4815 ≤ (5787035820169/12500000000000 : ℝ)^3791 := by
    have hnat : (1363370977 : ℕ)^4815*12500000000000^3791 ≤ 5787035820169^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363370977 2500000000 5787035820169 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1669661081/10000000000 : ℝ), (1295951077/2500000000 : ℝ), (1363370977/2500000000 : ℝ)] ![(5147777903271/50000000000000 : ℝ), (5426019702377/12500000000000 : ℝ), (5787035820169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1669661081/10000000000 : ℝ)|^4815 ≤ (5147777903271/50000000000000 : ℝ)^3791
        have hw : |(-1669661081/10000000000 : ℝ)|=(1669661081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295951077/2500000000 : ℝ)|^4815 ≤ (5426019702377/12500000000000 : ℝ)^3791
        have hw : |(1295951077/2500000000 : ℝ)|=(1295951077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363370977/2500000000 : ℝ)|^4815 ≤ (5787035820169/12500000000000 : ℝ)^3791
        have hw : |(1363370977/2500000000 : ℝ)|=(1363370977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_5 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639384591/5000000000 : ℝ)*x 0 + (-192371481/1250000000 : ℝ)*x 1 + (5453483927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639384591/5000000000 : ℝ)^4815 ≤ (44420661536969/100000000000000 : ℝ)^3791 := by
    have hnat : (2639384591 : ℕ)^4815*100000000000000^3791 ≤ 44420661536969^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639384591 5000000000 44420661536969 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192371481/1250000000 : ℝ)^4815 ≤ (9283051680071/100000000000000 : ℝ)^3791 := by
    have hnat : (192371481 : ℕ)^4815*100000000000000^3791 ≤ 9283051680071^3791*1250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192371481 1250000000 9283051680071 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453483927/10000000000 : ℝ)^4815 ≤ (46296286766217/100000000000000 : ℝ)^3791 := by
    have hnat : (5453483927 : ℕ)^4815*100000000000000^3791 ≤ 46296286766217^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453483927 10000000000 46296286766217 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639384591/5000000000 : ℝ), (-192371481/1250000000 : ℝ), (5453483927/10000000000 : ℝ)] ![(44420661536969/100000000000000 : ℝ), (9283051680071/100000000000000 : ℝ), (46296286766217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639384591/5000000000 : ℝ)|^4815 ≤ (44420661536969/100000000000000 : ℝ)^3791
        have hw : |(2639384591/5000000000 : ℝ)|=(2639384591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192371481/1250000000 : ℝ)|^4815 ≤ (9283051680071/100000000000000 : ℝ)^3791
        have hw : |(-192371481/1250000000 : ℝ)|=(192371481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453483927/10000000000 : ℝ)|^4815 ≤ (46296286766217/100000000000000 : ℝ)^3791
        have hw : |(5453483927/10000000000 : ℝ)|=(5453483927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_6 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055753841/2000000000 : ℝ)*x 0 + (68168549/125000000 : ℝ)*x 1 + (-769485913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055753841/2000000000 : ℝ)^4815 ≤ (5552582722849/12500000000000 : ℝ)^3791 := by
    have hnat : (1055753841 : ℕ)^4815*12500000000000^3791 ≤ 5552582722849^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055753841 2000000000 5552582722849 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68168549/125000000 : ℝ)^4815 ≤ (2314814334537/5000000000000 : ℝ)^3791 := by
    have hnat : (68168549 : ℕ)^4815*5000000000000^3791 ≤ 2314814334537^3791*125000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68168549 125000000 2314814334537 5000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769485913/5000000000 : ℝ)^4815 ≤ (4641525755761/50000000000000 : ℝ)^3791 := by
    have hnat : (769485913 : ℕ)^4815*50000000000000^3791 ≤ 4641525755761^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769485913 5000000000 4641525755761 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055753841/2000000000 : ℝ), (68168549/125000000 : ℝ), (-769485913/5000000000 : ℝ)] ![(5552582722849/12500000000000 : ℝ), (2314814334537/5000000000000 : ℝ), (4641525755761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055753841/2000000000 : ℝ)|^4815 ≤ (5552582722849/12500000000000 : ℝ)^3791
        have hw : |(1055753841/2000000000 : ℝ)|=(1055753841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68168549/125000000 : ℝ)|^4815 ≤ (2314814334537/5000000000000 : ℝ)^3791
        have hw : |(68168549/125000000 : ℝ)|=(68168549/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-769485913/5000000000 : ℝ)|^4815 ≤ (4641525755761/50000000000000 : ℝ)^3791
        have hw : |(-769485913/5000000000 : ℝ)|=(769485913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s3_7 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050317953/2500000000 : ℝ)*x 0 + (454912331/1000000000 : ℝ)*x 1 + (387419567/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050317953/2500000000 : ℝ)^4815 ≤ (4154902962279/12500000000000 : ℝ)^3791 := by
    have hnat : (1050317953 : ℕ)^4815*12500000000000^3791 ≤ 4154902962279^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050317953 2500000000 4154902962279 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454912331/1000000000 : ℝ)^4815 ≤ (36773027836301/100000000000000 : ℝ)^3791 := by
    have hnat : (454912331 : ℕ)^4815*100000000000000^3791 ≤ 36773027836301^3791*1000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454912331 1000000000 36773027836301 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387419567/1000000000 : ℝ)^4815 ≤ (29987748449673/100000000000000 : ℝ)^3791 := by
    have hnat : (387419567 : ℕ)^4815*100000000000000^3791 ≤ 29987748449673^3791*1000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387419567 1000000000 29987748449673 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050317953/2500000000 : ℝ), (454912331/1000000000 : ℝ), (387419567/1000000000 : ℝ)] ![(4154902962279/12500000000000 : ℝ), (36773027836301/100000000000000 : ℝ), (29987748449673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050317953/2500000000 : ℝ)|^4815 ≤ (4154902962279/12500000000000 : ℝ)^3791
        have hw : |(1050317953/2500000000 : ℝ)|=(1050317953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454912331/1000000000 : ℝ)|^4815 ≤ (36773027836301/100000000000000 : ℝ)^3791
        have hw : |(454912331/1000000000 : ℝ)|=(454912331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(387419567/1000000000 : ℝ)|^4815 ≤ (29987748449673/100000000000000 : ℝ)^3791
        have hw : |(387419567/1000000000 : ℝ)|=(387419567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1624_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2629/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8163/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16437/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2083/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16437/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2083/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16437/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2083/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16437/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2083/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16437/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2083/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16437/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2083/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2083/20000 : ℝ) ^ (4811/1024 : ℝ) ≤ (1212538017692743/50000000000000000000 : ℝ) := by
    have hpowers : (2083/20000 : ℝ)^4811 ≤ (1212538017692743/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2083 : ℕ)^4811*50000000000000000000^1024 ≤ 1212538017692743^1024*20000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2083 20000 1212538017692743 50000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2083/20000 : ℝ)) (X := (1212538017692743/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16437/100000 : ℝ) ^ (4811/1024 : ℝ) ≤ (20689235645137511/100000000000000000000 : ℝ) := by
    have hpowers : (16437/100000 : ℝ)^4811 ≤ (20689235645137511/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16437 : ℕ)^4811*100000000000000000000^1024 ≤ 20689235645137511^1024*100000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16437 100000 20689235645137511 100000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16437/100000 : ℝ)) (X := (20689235645137511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001212538017692743/25000000000000000000 : ℝ) ≤ (5000051615681939/5000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (25001212538017692743/25000000000000000000 : ℝ)^1024 ≤ (5000051615681939/5000000000000000 : ℝ)^4811 := by
      have hnat : (25001212538017692743 : ℕ)^1024*5000000000000000^4811 ≤ 5000051615681939^4811*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001212538017692743 25000000000000000000 5000051615681939 5000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000051615681939/5000000000000000 : ℝ)) (X := (25001212538017692743/25000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100023114311680522997/100000000000000000000 : ℝ) ≤ (5000245966558099/5000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (100023114311680522997/100000000000000000000 : ℝ)^1024 ≤ (5000245966558099/5000000000000000 : ℝ)^4811 := by
      have hnat : (100023114311680522997 : ℕ)^1024*5000000000000000^4811 ≤ 5000245966558099^4811*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100023114311680522997 100000000000000000000 5000245966558099 5000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000245966558099/5000000000000000 : ℝ)) (X := (100023114311680522997/100000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020689235645137511/50000000000000000000 : ℝ) ≤ (5000440317434259/5000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50020689235645137511/50000000000000000000 : ℝ)^1024 ≤ (5000440317434259/5000000000000000 : ℝ)^4811 := by
      have hnat : (50020689235645137511 : ℕ)^1024*5000000000000000^4811 ≤ 5000440317434259^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020689235645137511 50000000000000000000 5000440317434259 5000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000440317434259/5000000000000000 : ℝ)) (X := (50020689235645137511/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1212538017692743/50000000000000000000 : ℝ) ≤ ((15053131250443111929/15055000000000000000 : ℝ)+2*(75918311/117617187500 : ℝ)*(2083/20000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (15053131250443111929/15055000000000000000 : ℝ)+2*(75918311/117617187500 : ℝ)*(2083/20000 : ℝ)=(5000051615681939/5000000000000000 : ℝ) by norm_num, show 1+2*(1212538017692743/50000000000000000000 : ℝ)=(25001212538017692743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20689235645137511/100000000000000000000 : ℝ)+(1212538017692743/50000000000000000000 : ℝ) ≤ ((15053131250443111929/15055000000000000000 : ℝ)+(75918311/117617187500 : ℝ)*((16437/100000 : ℝ)+(2083/20000 : ℝ)))^(4811/1024 : ℝ) := by
    rw [show (15053131250443111929/15055000000000000000 : ℝ)+(75918311/117617187500 : ℝ)*((16437/100000 : ℝ)+(2083/20000 : ℝ))=(5000245966558099/5000000000000000 : ℝ) by norm_num, show 1+(20689235645137511/100000000000000000000 : ℝ)+(1212538017692743/50000000000000000000 : ℝ)=(100023114311680522997/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20689235645137511/100000000000000000000 : ℝ) ≤ ((15053131250443111929/15055000000000000000 : ℝ)+2*(75918311/117617187500 : ℝ)*(16437/100000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (15053131250443111929/15055000000000000000 : ℝ)+2*(75918311/117617187500 : ℝ)*(16437/100000 : ℝ)=(5000440317434259/5000000000000000 : ℝ) by norm_num, show 1+2*(20689235645137511/100000000000000000000 : ℝ)=(50020689235645137511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15053131250443111929/15055000000000000000 : ℝ)*(X 1 0+X 2 0)+(75918311/117617187500 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (16437/100000 : ℝ)) (c := (15053131250443111929/15055000000000000000 : ℝ)) (alpha := (75918311/117617187500 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15053131250443111929/15055000000000000000 : ℝ)*(X 0 1+X 2 1)+(75918311/117617187500 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (16437/100000 : ℝ)) (c := (15053131250443111929/15055000000000000000 : ℝ)) (alpha := (75918311/117617187500 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15053131250443111929/15055000000000000000 : ℝ)*(X 0 2+X 1 2)+(75918311/117617187500 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (2083/20000 : ℝ)) (hi := (16437/100000 : ℝ)) (c := (15053131250443111929/15055000000000000000 : ℝ)) (alpha := (75918311/117617187500 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1669592511/10000000000 : ℝ)*X 0 0+(1363889537/2500000000 : ℝ)*X 0 1+(1295437933/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351657491/10000000000 : ℝ)*X 1 0+(-1810704061/10000000000 : ℝ)*X 1 1+(5181751743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2140663/4000000 : ℝ)*X 2 0+(2590875877/5000000000 : ℝ)*X 2 1+(-905352017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050275069/2500000000 : ℝ)*X 0 0+(1934502297/5000000000 : ℝ)*X 0 1+(4554260221/10000000000 : ℝ)*X 0 2+(1050275069/2500000000 : ℝ)*X 1 0+(1934502297/5000000000 : ℝ)*X 1 1+(4554260221/10000000000 : ℝ)*X 1 2+(1050275069/2500000000 : ℝ)*X 2 0+(1934502297/5000000000 : ℝ)*X 2 1+(4554260221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1669661081/10000000000 : ℝ)*X 0 0+(1295951077/2500000000 : ℝ)*X 0 1+(1363370977/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639384591/5000000000 : ℝ)*X 1 0+(-192371481/1250000000 : ℝ)*X 1 1+(5453483927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055753841/2000000000 : ℝ)*X 2 0+(68168549/125000000 : ℝ)*X 2 1+(-769485913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050317953/2500000000 : ℝ)*X 0 0+(454912331/1000000000 : ℝ)*X 0 1+(387419567/1000000000 : ℝ)*X 0 2+(1050317953/2500000000 : ℝ)*X 1 0+(454912331/1000000000 : ℝ)*X 1 1+(387419567/1000000000 : ℝ)*X 1 2+(1050317953/2500000000 : ℝ)*X 2 0+(454912331/1000000000 : ℝ)*X 2 1+(387419567/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (491896792409635504342232691/150550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484096741/100000000000000 : ℝ)*(base19) + (440292109/100000000000000 : ℝ)*(base23) + (26729743/100000000000000 : ℝ)*(lower2) + (110539/156250000000 : ℝ)*(upper3) + (55935157/100000000000000 : ℝ)*(upper5) + (511154176065469/20000000000000 : ℝ)*(major0) + (511154176065469/20000000000000 : ℝ)*(major1) + (511154176065469/20000000000000 : ℝ)*(major2) + (913055329806049/25000000000000 : ℝ)*(sp0) + (913056740826399/25000000000000 : ℝ)*(sp1) + (913056751777557/25000000000000 : ℝ)*(sp2) + (45603489910167/3125000000000 : ℝ)*(sp3) + (6128178141/100000000000000 : ℝ)*(sp4) + (1263607971/50000000000000 : ℝ)*(sp7) + (729657102170643/50000000000000 : ℝ)*(f.failure) + (3652227447402337/100000000000000 : ℝ)*(f.sum) + (7565469158059/3011000000000000000000000000 : ℝ)*base65 + (1201122843279679701/301100000000000000000000000000000 : ℝ)*base67 + (2917737340220479701/301100000000000000000000000000000 : ℝ)*base69 + (279659680718479701/301100000000000000000000000000000 : ℝ)*base71 + (40603905599/75275000000000000000000000 : ℝ)*base74 + (3130166001359679701/301100000000000000000000000000000 : ℝ)*base75 + (265420552118079701/301100000000000000000000000000000 : ℝ)*base77 + (2593240785056079701/301100000000000000000000000000000 : ℝ)*base79 + (5770395576627/752750000000000000000000000 : ℝ)*base81 + (9420641/1000000000000000000000 : ℝ)*base90 + (9420641/1000000000000000000000 : ℝ)*base92 + (9420641/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92427831005480689253813979/9409375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (297688373/20000000000000 : ℝ)*(base19) + (1630554917/100000000000000 : ℝ)*(base23) + (216787619/100000000000000 : ℝ)*(upper3) + (26173743/50000000000000 : ℝ)*(lower4) + (194226919/100000000000000 : ℝ)*(upper5) + (8108974132327/312500000000 : ℝ)*(major0) + (8108974132327/312500000000 : ℝ)*(major1) + (8108974132327/312500000000 : ℝ)*(major2) + (859265649/5000000000000 : ℝ)*(sp1) + (9562778267/50000000000000 : ℝ)*(sp2) + (3708102805910073/100000000000000 : ℝ)*(sp4) + (927021033038807/25000000000000 : ℝ)*(sp5) + (1854041024899311/50000000000000 : ℝ)*(sp6) + (185205038918437/12500000000000 : ℝ)*(sp7) + (185205038918437/12500000000000 : ℝ)*(f.failure) + (3708102805910073/100000000000000 : ℝ)*(f.sum) + (11879229312749/3011000000000000000000000000 : ℝ)*base66 + (6163210826910033/4704687500000000000000000000000 : ℝ)*base67 + (15884937165214967/4704687500000000000000000000000 : ℝ)*base70 + (8076733394060033/4704687500000000000000000000000 : ℝ)*base71 + (1958175159129/752750000000000000000000000 : ℝ)*base74 + (4038248051671217/4704687500000000000000000000000 : ℝ)*base76 + (23522773912519079/2352343750000000000000000000000 : ℝ)*base77 + (23486696382672533/4704687500000000000000000000000 : ℝ)*base79 + (1868974235479/376375000000000000000000000 : ℝ)*base82 + (1261319/250000000000000000000 : ℝ)*base90 + (1261319/250000000000000000000 : ℝ)*base92 + (1261319/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1624_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2629/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1624_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1624_s4_0 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1669674673/10000000000 : ℝ)*x 0 + (272756861/500000000 : ℝ)*x 1 + (129552951/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669674673/10000000000 : ℝ)^4815 ≤ (1029566225707/10000000000000 : ℝ)^3791 := by
    have hnat : (1669674673 : ℕ)^4815*10000000000000^3791 ≤ 1029566225707^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669674673 10000000000 1029566225707 10000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272756861/500000000 : ℝ)^4815 ≤ (23157056964623/50000000000000 : ℝ)^3791 := by
    have hnat : (272756861 : ℕ)^4815*50000000000000^3791 ≤ 23157056964623^3791*500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272756861 500000000 23157056964623 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129552951/250000000 : ℝ)^4815 ≤ (271188898751/625000000000 : ℝ)^3791 := by
    have hnat : (129552951 : ℕ)^4815*625000000000^3791 ≤ 271188898751^3791*250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129552951 250000000 271188898751 625000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1669674673/10000000000 : ℝ), (272756861/500000000 : ℝ), (129552951/250000000 : ℝ)] ![(1029566225707/10000000000000 : ℝ), (23157056964623/50000000000000 : ℝ), (271188898751/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1669674673/10000000000 : ℝ)|^4815 ≤ (1029566225707/10000000000000 : ℝ)^3791
        have hw : |(-1669674673/10000000000 : ℝ)|=(1669674673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272756861/500000000 : ℝ)|^4815 ≤ (23157056964623/50000000000000 : ℝ)^3791
        have hw : |(272756861/500000000 : ℝ)|=(272756861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129552951/250000000 : ℝ)|^4815 ≤ (271188898751/625000000000 : ℝ)^3791
        have hw : |(129552951/250000000 : ℝ)|=(129552951/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_1 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675772527/5000000000 : ℝ)*x 0 + (-1810368799/10000000000 : ℝ)*x 1 + (5182117527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675772527/5000000000 : ℝ)^4815 ≤ (1807997226589/4000000000000 : ℝ)^3791 := by
    have hnat : (2675772527 : ℕ)^4815*4000000000000^3791 ≤ 1807997226589^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675772527 5000000000 1807997226589 4000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1810368799/10000000000 : ℝ)^4815 ≤ (5704925490847/50000000000000 : ℝ)^3791 := by
    have hnat : (1810368799 : ℕ)^4815*50000000000000^3791 ≤ 5704925490847^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810368799 10000000000 5704925490847 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182117527/10000000000 : ℝ)^4815 ≤ (8678043668907/20000000000000 : ℝ)^3791 := by
    have hnat : (5182117527 : ℕ)^4815*20000000000000^3791 ≤ 8678043668907^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182117527 10000000000 8678043668907 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675772527/5000000000 : ℝ), (-1810368799/10000000000 : ℝ), (5182117527/10000000000 : ℝ)] ![(1807997226589/4000000000000 : ℝ), (5704925490847/50000000000000 : ℝ), (8678043668907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675772527/5000000000 : ℝ)|^4815 ≤ (1807997226589/4000000000000 : ℝ)^3791
        have hw : |(2675772527/5000000000 : ℝ)|=(2675772527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1810368799/10000000000 : ℝ)|^4815 ≤ (5704925490847/50000000000000 : ℝ)^3791
        have hw : |(-1810368799/10000000000 : ℝ)|=(1810368799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182117527/10000000000 : ℝ)|^4815 ≤ (8678043668907/20000000000000 : ℝ)^3791
        have hw : |(5182117527/10000000000 : ℝ)|=(5182117527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_2 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070308961/2000000000 : ℝ)*x 0 + (2591058913/5000000000 : ℝ)*x 1 + (-905184367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070308961/2000000000 : ℝ)^4815 ≤ (22599963996781/50000000000000 : ℝ)^3791 := by
    have hnat : (1070308961 : ℕ)^4815*50000000000000^3791 ≤ 22599963996781^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070308961 2000000000 22599963996781 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591058913/5000000000 : ℝ)^4815 ≤ (10847555381081/25000000000000 : ℝ)^3791 := by
    have hnat : (2591058913 : ℕ)^4815*25000000000000^3791 ≤ 10847555381081^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591058913 5000000000 10847555381081 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905184367/5000000000 : ℝ)^4815 ≤ (178278913459/1562500000000 : ℝ)^3791 := by
    have hnat : (905184367 : ℕ)^4815*1562500000000^3791 ≤ 178278913459^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905184367 5000000000 178278913459 1562500000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070308961/2000000000 : ℝ), (2591058913/5000000000 : ℝ), (-905184367/5000000000 : ℝ)] ![(22599963996781/50000000000000 : ℝ), (10847555381081/25000000000000 : ℝ), (178278913459/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070308961/2000000000 : ℝ)|^4815 ≤ (22599963996781/50000000000000 : ℝ)^3791
        have hw : |(1070308961/2000000000 : ℝ)|=(1070308961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591058913/5000000000 : ℝ)|^4815 ≤ (10847555381081/25000000000000 : ℝ)^3791
        have hw : |(2591058913/5000000000 : ℝ)|=(2591058913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-905184367/5000000000 : ℝ)|^4815 ≤ (178278913459/1562500000000 : ℝ)^3791
        have hw : |(-905184367/5000000000 : ℝ)|=(905184367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_3 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420115499/1000000000 : ℝ)*x 0 + (1934991539/5000000000 : ℝ)*x 1 + (910654061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420115499/1000000000 : ℝ)^4815 ≤ (16619024893031/50000000000000 : ℝ)^3791 := by
    have hnat : (420115499 : ℕ)^4815*50000000000000^3791 ≤ 16619024893031^3791*1000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420115499 1000000000 16619024893031 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934991539/5000000000 : ℝ)^4815 ≤ (1497316993119/5000000000000 : ℝ)^3791 := by
    have hnat : (1934991539 : ℕ)^4815*5000000000000^3791 ≤ 1497316993119^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934991539 5000000000 1497316993119 5000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910654061/2000000000 : ℝ)^4815 ≤ (36815610336247/100000000000000 : ℝ)^3791 := by
    have hnat : (910654061 : ℕ)^4815*100000000000000^3791 ≤ 36815610336247^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910654061 2000000000 36815610336247 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420115499/1000000000 : ℝ), (1934991539/5000000000 : ℝ), (910654061/2000000000 : ℝ)] ![(16619024893031/50000000000000 : ℝ), (1497316993119/5000000000000 : ℝ), (36815610336247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420115499/1000000000 : ℝ)|^4815 ≤ (16619024893031/50000000000000 : ℝ)^3791
        have hw : |(420115499/1000000000 : ℝ)|=(420115499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1934991539/5000000000 : ℝ)|^4815 ≤ (1497316993119/5000000000000 : ℝ)^3791
        have hw : |(1934991539/5000000000 : ℝ)|=(1934991539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910654061/2000000000 : ℝ)|^4815 ≤ (36815610336247/100000000000000 : ℝ)^3791
        have hw : |(910654061/2000000000 : ℝ)|=(910654061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_4 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-417435691/2500000000 : ℝ)*x 0 + (5184158649/10000000000 : ℝ)*x 1 + (5453075049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417435691/2500000000 : ℝ)^4815 ≤ (10296195539211/100000000000000 : ℝ)^3791 := by
    have hnat : (417435691 : ℕ)^4815*100000000000000^3791 ≤ 10296195539211^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417435691 2500000000 10296195539211 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184158649/10000000000 : ℝ)^4815 ≤ (8682385262259/20000000000000 : ℝ)^3791 := by
    have hnat : (5184158649 : ℕ)^4815*20000000000000^3791 ≤ 8682385262259^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184158649 10000000000 8682385262259 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453075049/10000000000 : ℝ)^4815 ≤ (5786484766617/12500000000000 : ℝ)^3791 := by
    have hnat : (5453075049 : ℕ)^4815*12500000000000^3791 ≤ 5786484766617^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453075049 10000000000 5786484766617 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417435691/2500000000 : ℝ), (5184158649/10000000000 : ℝ), (5453075049/10000000000 : ℝ)] ![(10296195539211/100000000000000 : ℝ), (8682385262259/20000000000000 : ℝ), (5786484766617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417435691/2500000000 : ℝ)|^4815 ≤ (10296195539211/100000000000000 : ℝ)^3791
        have hw : |(-417435691/2500000000 : ℝ)|=(417435691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184158649/10000000000 : ℝ)|^4815 ≤ (8682385262259/20000000000000 : ℝ)^3791
        have hw : |(5184158649/10000000000 : ℝ)|=(5184158649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453075049/10000000000 : ℝ)|^4815 ≤ (5786484766617/12500000000000 : ℝ)^3791
        have hw : |(5453075049/10000000000 : ℝ)|=(5453075049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_5 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319716651/2500000000 : ℝ)*x 0 + (-192426391/1250000000 : ℝ)*x 1 + (340817201/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319716651/2500000000 : ℝ)^4815 ≤ (44421702782091/100000000000000 : ℝ)^3791 := by
    have hnat : (1319716651 : ℕ)^4815*100000000000000^3791 ≤ 44421702782091^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319716651 2500000000 44421702782091 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192426391/1250000000 : ℝ)^4815 ≤ (9286417266681/100000000000000 : ℝ)^3791 := by
    have hnat : (192426391 : ℕ)^4815*100000000000000^3791 ≤ 9286417266681^3791*1250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192426391 1250000000 9286417266681 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340817201/625000000 : ℝ)^4815 ≤ (46291879933557/100000000000000 : ℝ)^3791 := by
    have hnat : (340817201 : ℕ)^4815*100000000000000^3791 ≤ 46291879933557^3791*625000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340817201 625000000 46291879933557 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319716651/2500000000 : ℝ), (-192426391/1250000000 : ℝ), (340817201/625000000 : ℝ)] ![(44421702782091/100000000000000 : ℝ), (9286417266681/100000000000000 : ℝ), (46291879933557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319716651/2500000000 : ℝ)|^4815 ≤ (44421702782091/100000000000000 : ℝ)^3791
        have hw : |(1319716651/2500000000 : ℝ)|=(1319716651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192426391/1250000000 : ℝ)|^4815 ≤ (9286417266681/100000000000000 : ℝ)^3791
        have hw : |(-192426391/1250000000 : ℝ)|=(192426391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340817201/625000000 : ℝ)|^4815 ≤ (46291879933557/100000000000000 : ℝ)^3791
        have hw : |(340817201/625000000 : ℝ)|=(340817201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_6 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278866601/10000000000 : ℝ)*x 0 + (5453075131/10000000000 : ℝ)*x 1 + (-384852813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278866601/10000000000 : ℝ)^4815 ≤ (44421702750027/100000000000000 : ℝ)^3791 := by
    have hnat : (5278866601 : ℕ)^4815*100000000000000^3791 ≤ 44421702750027^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278866601 10000000000 44421702750027 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453075131/10000000000 : ℝ)^4815 ≤ (46291879017073/100000000000000 : ℝ)^3791 := by
    have hnat : (5453075131 : ℕ)^4815*100000000000000^3791 ≤ 46291879017073^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453075131 10000000000 46291879017073 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384852813/2500000000 : ℝ)^4815 ≤ (2321604554189/25000000000000 : ℝ)^3791 := by
    have hnat : (384852813 : ℕ)^4815*25000000000000^3791 ≤ 2321604554189^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384852813 2500000000 2321604554189 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278866601/10000000000 : ℝ), (5453075131/10000000000 : ℝ), (-384852813/2500000000 : ℝ)] ![(44421702750027/100000000000000 : ℝ), (46291879017073/100000000000000 : ℝ), (2321604554189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278866601/10000000000 : ℝ)|^4815 ≤ (44421702750027/100000000000000 : ℝ)^3791
        have hw : |(5278866601/10000000000 : ℝ)|=(5278866601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453075131/10000000000 : ℝ)|^4815 ≤ (46291879017073/100000000000000 : ℝ)^3791
        have hw : |(5453075131/10000000000 : ℝ)|=(5453075131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384852813/2500000000 : ℝ)|^4815 ≤ (2321604554189/25000000000000 : ℝ)^3791
        have hw : |(-384852813/2500000000 : ℝ)|=(384852813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s4_7 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201324783/10000000000 : ℝ)*x 0 + (90963251/200000000 : ℝ)*x 1 + (3875144821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201324783/10000000000 : ℝ)^4815 ≤ (16619877996079/50000000000000 : ℝ)^3791 := by
    have hnat : (4201324783 : ℕ)^4815*50000000000000^3791 ≤ 16619877996079^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201324783 10000000000 16619877996079 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90963251/200000000 : ℝ)^4815 ≤ (2297697748783/6250000000000 : ℝ)^3791 := by
    have hnat : (90963251 : ℕ)^4815*6250000000000^3791 ≤ 2297697748783^3791*200000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90963251 200000000 2297697748783 6250000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3875144821/10000000000 : ℝ)^4815 ≤ (29997080014839/100000000000000 : ℝ)^3791 := by
    have hnat : (3875144821 : ℕ)^4815*100000000000000^3791 ≤ 29997080014839^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875144821 10000000000 29997080014839 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201324783/10000000000 : ℝ), (90963251/200000000 : ℝ), (3875144821/10000000000 : ℝ)] ![(16619877996079/50000000000000 : ℝ), (2297697748783/6250000000000 : ℝ), (29997080014839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201324783/10000000000 : ℝ)|^4815 ≤ (16619877996079/50000000000000 : ℝ)^3791
        have hw : |(4201324783/10000000000 : ℝ)|=(4201324783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90963251/200000000 : ℝ)|^4815 ≤ (2297697748783/6250000000000 : ℝ)^3791
        have hw : |(90963251/200000000 : ℝ)|=(90963251/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3875144821/10000000000 : ℝ)|^4815 ≤ (29997080014839/100000000000000 : ℝ)^3791
        have hw : |(3875144821/10000000000 : ℝ)|=(3875144821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1624_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2629/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10523/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16317/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2629/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2629/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2629/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8163/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2629/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2629/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8163/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2629/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2629/25000 : ℝ) ^ (4811/1024 : ℝ) ≤ (2537564659119653/100000000000000000000 : ℝ) := by
    have hpowers : (2629/25000 : ℝ)^4811 ≤ (2537564659119653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2629 : ℕ)^4811*100000000000000000000^1024 ≤ 2537564659119653^1024*25000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2629 25000 2537564659119653 100000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2629/25000 : ℝ)) (X := (2537564659119653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8163/50000 : ℝ) ^ (4811/1024 : ℝ) ≤ (5010241288458447/25000000000000000000 : ℝ) := by
    have hpowers : (8163/50000 : ℝ)^4811 ≤ (5010241288458447/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8163 : ℕ)^4811*25000000000000000000^1024 ≤ 5010241288458447^1024*50000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8163 50000 5010241288458447 25000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8163/50000 : ℝ)) (X := (5010241288458447/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002537564659119653/50000000000000000000 : ℝ) ≤ (5000054009858851/5000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50002537564659119653/50000000000000000000 : ℝ)^1024 ≤ (5000054009858851/5000000000000000 : ℝ)^4811 := by
      have hnat : (50002537564659119653 : ℕ)^1024*5000000000000000^4811 ≤ 5000054009858851^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002537564659119653 50000000000000000000 5000054009858851 5000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000054009858851/5000000000000000 : ℝ)) (X := (50002537564659119653/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022578529812953441/100000000000000000000 : ℝ) ≤ (1000048053128733/1000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (100022578529812953441/100000000000000000000 : ℝ)^1024 ≤ (1000048053128733/1000000000000000 : ℝ)^4811 := by
      have hnat : (100022578529812953441 : ℕ)^1024*1000000000000000^4811 ≤ 1000048053128733^4811*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022578529812953441 100000000000000000000 1000048053128733 1000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000048053128733/1000000000000000 : ℝ)) (X := (100022578529812953441/100000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505010241288458447/12500000000000000000 : ℝ) ≤ (5000426521428479/5000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (12505010241288458447/12500000000000000000 : ℝ)^1024 ≤ (5000426521428479/5000000000000000 : ℝ)^4811 := by
      have hnat : (12505010241288458447 : ℕ)^1024*5000000000000000^4811 ≤ 5000426521428479^4811*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505010241288458447 12500000000000000000 5000426521428479 5000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000426521428479/5000000000000000 : ℝ)) (X := (12505010241288458447/12500000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2537564659119653/100000000000000000000 : ℝ) ≤ ((14523198232806858131/14525000000000000000 : ℝ)+2*(93127892407/145250000000000 : ℝ)*(2629/25000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (14523198232806858131/14525000000000000000 : ℝ)+2*(93127892407/145250000000000 : ℝ)*(2629/25000 : ℝ)=(5000054009858851/5000000000000000 : ℝ) by norm_num, show 1+2*(2537564659119653/100000000000000000000 : ℝ)=(50002537564659119653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5010241288458447/25000000000000000000 : ℝ)+(2537564659119653/100000000000000000000 : ℝ) ≤ ((14523198232806858131/14525000000000000000 : ℝ)+(93127892407/145250000000000 : ℝ)*((8163/50000 : ℝ)+(2629/25000 : ℝ)))^(4811/1024 : ℝ) := by
    rw [show (14523198232806858131/14525000000000000000 : ℝ)+(93127892407/145250000000000 : ℝ)*((8163/50000 : ℝ)+(2629/25000 : ℝ))=(1000048053128733/1000000000000000 : ℝ) by norm_num, show 1+(5010241288458447/25000000000000000000 : ℝ)+(2537564659119653/100000000000000000000 : ℝ)=(100022578529812953441/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5010241288458447/25000000000000000000 : ℝ) ≤ ((14523198232806858131/14525000000000000000 : ℝ)+2*(93127892407/145250000000000 : ℝ)*(8163/50000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (14523198232806858131/14525000000000000000 : ℝ)+2*(93127892407/145250000000000 : ℝ)*(8163/50000 : ℝ)=(5000426521428479/5000000000000000 : ℝ) by norm_num, show 1+2*(5010241288458447/25000000000000000000 : ℝ)=(12505010241288458447/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14523198232806858131/14525000000000000000 : ℝ)*(X 1 0+X 2 0)+(93127892407/145250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (2629/25000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (14523198232806858131/14525000000000000000 : ℝ)) (alpha := (93127892407/145250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14523198232806858131/14525000000000000000 : ℝ)*(X 0 1+X 2 1)+(93127892407/145250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (2629/25000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (14523198232806858131/14525000000000000000 : ℝ)) (alpha := (93127892407/145250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14523198232806858131/14525000000000000000 : ℝ)*(X 0 2+X 1 2)+(93127892407/145250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (2629/25000 : ℝ)) (hi := (8163/50000 : ℝ)) (c := (14523198232806858131/14525000000000000000 : ℝ)) (alpha := (93127892407/145250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1669674673/10000000000 : ℝ)*X 0 0+(272756861/500000000 : ℝ)*X 0 1+(129552951/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675772527/5000000000 : ℝ)*X 1 0+(-1810368799/10000000000 : ℝ)*X 1 1+(5182117527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070308961/2000000000 : ℝ)*X 2 0+(2591058913/5000000000 : ℝ)*X 2 1+(-905184367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((420115499/1000000000 : ℝ)*X 0 0+(1934991539/5000000000 : ℝ)*X 0 1+(910654061/2000000000 : ℝ)*X 0 2+(420115499/1000000000 : ℝ)*X 1 0+(1934991539/5000000000 : ℝ)*X 1 1+(910654061/2000000000 : ℝ)*X 1 2+(420115499/1000000000 : ℝ)*X 2 0+(1934991539/5000000000 : ℝ)*X 2 1+(910654061/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-417435691/2500000000 : ℝ)*X 0 0+(5184158649/10000000000 : ℝ)*X 0 1+(5453075049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319716651/2500000000 : ℝ)*X 1 0+(-192426391/1250000000 : ℝ)*X 1 1+(340817201/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278866601/10000000000 : ℝ)*X 2 0+(5453075131/10000000000 : ℝ)*X 2 1+(-384852813/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201324783/10000000000 : ℝ)*X 0 0+(90963251/200000000 : ℝ)*X 0 1+(3875144821/10000000000 : ℝ)*X 0 2+(4201324783/10000000000 : ℝ)*X 1 0+(90963251/200000000 : ℝ)*X 1 1+(3875144821/10000000000 : ℝ)*X 1 2+(4201324783/10000000000 : ℝ)*X 2 0+(90963251/200000000 : ℝ)*X 2 1+(3875144821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (325187625564951447612609753/25937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (440240511/20000000000000 : ℝ)*(base19) + (36694581/2000000000000 : ℝ)*(base23) + (10491653/10000000000000 : ℝ)*(lower2) + (306239689/100000000000000 : ℝ)*(upper3) + (47115487/25000000000000 : ℝ)*(upper5) + (640790595007451/25000000000000 : ℝ)*(major0) + (640790595007451/25000000000000 : ℝ)*(major1) + (640790595007451/25000000000000 : ℝ)*(major2) + (366276877836099/10000000000000 : ℝ)*(sp0) + (915696869959197/25000000000000 : ℝ)*(sp1) + (3662787846310293/100000000000000 : ℝ)*(sp2) + (1463523385905523/100000000000000 : ℝ)*(sp3) + (20902678353/100000000000000 : ℝ)*(sp4) + (11275202921/100000000000000 : ℝ)*(sp7) + (365883665277111/25000000000000 : ℝ)*(f.failure) + (3662789681039343/100000000000000 : ℝ)*(f.sum) + (8188616838117/2075000000000000000000000000 : ℝ)*base66 + (654761413023215583/51875000000000000000000000000000 : ℝ)*base67 + (1038088129963215583/51875000000000000000000000000000 : ℝ)*base69 + (392339990153215583/51875000000000000000000000000000 : ℝ)*base71 + (1360362295923/518750000000000000000000000 : ℝ)*base74 + (713028518427590583/51875000000000000000000000000000 : ℝ)*base75 + (424838053291340583/51875000000000000000000000000000 : ℝ)*base77 + (677196825496340583/51875000000000000000000000000000 : ℝ)*base79 + (4866443538829/1037500000000000000000000000 : ℝ)*base81 + (4400557/500000000000000000000 : ℝ)*base90 + (4400557/500000000000000000000 : ℝ)*base92 + (4400557/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (727080941933639751005604969/103750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1270868417/100000000000000 : ℝ)*(base19) + (1293390517/100000000000000 : ℝ)*(base23) + (467010587/100000000000000 : ℝ)*(lower1) + (2157449/12500000000000 : ℝ)*(upper2) + (157081523/100000000000000 : ℝ)*(upper3) + (23025871/20000000000000 : ℝ)*(upper5) + (2602223776950231/100000000000000 : ℝ)*(major0) + (2602223776950231/100000000000000 : ℝ)*(major1) + (2602223776950231/100000000000000 : ℝ)*(major2) + (585440857/100000000000000 : ℝ)*(sp1) + (929652268714463/25000000000000 : ℝ)*(sp4) + (3718607218548577/100000000000000 : ℝ)*(sp5) + (1859303890733667/50000000000000 : ℝ)*(sp6) + (14858382454423/1000000000000 : ℝ)*(sp7) + (14858382454423/1000000000000 : ℝ)*(f.failure) + (929652268714463/25000000000000 : ℝ)*(f.sum) + (5113735746519/1037500000000000000000000000 : ℝ)*base66 + (1187454006586231677/207500000000000000000000000000000 : ℝ)*base68 + (2526581002663768323/207500000000000000000000000000000 : ℝ)*base69 + (285324462221231677/207500000000000000000000000000000 : ℝ)*base72 + (8878599958213/2075000000000000000000000000 : ℝ)*base74 + (275323546641268323/207500000000000000000000000000000 : ℝ)*base75 + (505319686431231677/207500000000000000000000000000000 : ℝ)*base78 + (1152782583831231677/207500000000000000000000000000000 : ℝ)*base80 + (9838353037481/1037500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (128499/20000000000000000000 : ℝ)*base89 + (128499/20000000000000000000 : ℝ)*base91 + (128499/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1624_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8163/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2629/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1624_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1624_s5_0 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1669682319/10000000000 : ℝ)*x 0 + (2727552753/5000000000 : ℝ)*x 1 + (5182144567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669682319/10000000000 : ℝ)^4815 ≤ (1286965267439/12500000000000 : ℝ)^3791 := by
    have hnat : (1669682319 : ℕ)^4815*12500000000000^3791 ≤ 1286965267439^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669682319 10000000000 1286965267439 12500000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727552753/5000000000 : ℝ)^4815 ≤ (144730537341/312500000000 : ℝ)^3791 := by
    have hnat : (2727552753 : ℕ)^4815*312500000000^3791 ≤ 144730537341^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727552753 5000000000 144730537341 312500000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182144567/10000000000 : ℝ)^4815 ≤ (8678101181649/20000000000000 : ℝ)^3791 := by
    have hnat : (5182144567 : ℕ)^4815*20000000000000^3791 ≤ 8678101181649^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182144567 10000000000 8678101181649 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1669682319/10000000000 : ℝ), (2727552753/5000000000 : ℝ), (5182144567/10000000000 : ℝ)] ![(1286965267439/12500000000000 : ℝ), (144730537341/312500000000 : ℝ), (8678101181649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1669682319/10000000000 : ℝ)|^4815 ≤ (1286965267439/12500000000000 : ℝ)^3791
        have hw : |(-1669682319/10000000000 : ℝ)|=(1669682319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727552753/5000000000 : ℝ)|^4815 ≤ (144730537341/312500000000 : ℝ)^3791
        have hw : |(2727552753/5000000000 : ℝ)|=(2727552753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182144567/10000000000 : ℝ)|^4815 ≤ (8678101181649/20000000000000 : ℝ)^3791
        have hw : |(5182144567/10000000000 : ℝ)|=(5182144567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_1 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675767907/5000000000 : ℝ)*x 0 + (-905172523/5000000000 : ℝ)*x 1 + (2591072363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675767907/5000000000 : ℝ)^4815 ≤ (22599915771031/50000000000000 : ℝ)^3791 := by
    have hnat : (2675767907 : ℕ)^4815*50000000000000^3791 ≤ 22599915771031^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675767907 5000000000 22599915771031 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905172523/5000000000 : ℝ)^4815 ≤ (2281932168371/20000000000000 : ℝ)^3791 := by
    have hnat : (905172523 : ℕ)^4815*20000000000000^3791 ≤ 2281932168371^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905172523 5000000000 2281932168371 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591072363/5000000000 : ℝ)^4815 ≤ (10847626899793/25000000000000 : ℝ)^3791 := by
    have hnat : (2591072363 : ℕ)^4815*25000000000000^3791 ≤ 10847626899793^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591072363 5000000000 10847626899793 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675767907/5000000000 : ℝ), (-905172523/5000000000 : ℝ), (2591072363/5000000000 : ℝ)] ![(22599915771031/50000000000000 : ℝ), (2281932168371/20000000000000 : ℝ), (10847626899793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675767907/5000000000 : ℝ)|^4815 ≤ (22599915771031/50000000000000 : ℝ)^3791
        have hw : |(2675767907/5000000000 : ℝ)|=(2675767907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-905172523/5000000000 : ℝ)|^4815 ≤ (2281932168371/20000000000000 : ℝ)^3791
        have hw : |(-905172523/5000000000 : ℝ)|=(905172523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591072363/5000000000 : ℝ)|^4815 ≤ (10847626899793/25000000000000 : ℝ)^3791
        have hw : |(2591072363/5000000000 : ℝ)|=(2591072363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_2 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351535839/10000000000 : ℝ)*x 0 + (1036428971/2000000000 : ℝ)*x 1 + (-905172421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351535839/10000000000 : ℝ)^4815 ≤ (45199831810251/100000000000000 : ℝ)^3791 := by
    have hnat : (5351535839 : ℕ)^4815*100000000000000^3791 ≤ 45199831810251^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351535839 10000000000 45199831810251 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036428971/2000000000 : ℝ)^4815 ≤ (2711906810691/6250000000000 : ℝ)^3791 := by
    have hnat : (1036428971 : ℕ)^4815*6250000000000^3791 ≤ 2711906810691^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036428971 2000000000 2711906810691 6250000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905172421/5000000000 : ℝ)^4815 ≤ (11409659208863/100000000000000 : ℝ)^3791 := by
    have hnat : (905172421 : ℕ)^4815*100000000000000^3791 ≤ 11409659208863^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905172421 5000000000 11409659208863 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351535839/10000000000 : ℝ), (1036428971/2000000000 : ℝ), (-905172421/5000000000 : ℝ)] ![(45199831810251/100000000000000 : ℝ), (2711906810691/6250000000000 : ℝ), (11409659208863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351535839/10000000000 : ℝ)|^4815 ≤ (45199831810251/100000000000000 : ℝ)^3791
        have hw : |(5351535839/10000000000 : ℝ)|=(5351535839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036428971/2000000000 : ℝ)|^4815 ≤ (2711906810691/6250000000000 : ℝ)^3791
        have hw : |(1036428971/2000000000 : ℝ)|=(1036428971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-905172421/5000000000 : ℝ)|^4815 ≤ (11409659208863/100000000000000 : ℝ)^3791
        have hw : |(-905172421/5000000000 : ℝ)|=(905172421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_3 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525144859/1250000000 : ℝ)*x 0 + (3870056571/10000000000 : ℝ)*x 1 + (1138299043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525144859/1250000000 : ℝ)^4815 ≤ (33238088795071/100000000000000 : ℝ)^3791 := by
    have hnat : (525144859 : ℕ)^4815*100000000000000^3791 ≤ 33238088795071^3791*1250000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525144859 1250000000 33238088795071 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3870056571/10000000000 : ℝ)^4815 ≤ (5989412434693/20000000000000 : ℝ)^3791 := by
    have hnat : (3870056571 : ℕ)^4815*20000000000000^3791 ≤ 5989412434693^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870056571 10000000000 5989412434693 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1138299043/2500000000 : ℝ)^4815 ≤ (18407424512979/50000000000000 : ℝ)^3791 := by
    have hnat : (1138299043 : ℕ)^4815*50000000000000^3791 ≤ 18407424512979^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138299043 2500000000 18407424512979 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525144859/1250000000 : ℝ), (3870056571/10000000000 : ℝ), (1138299043/2500000000 : ℝ)] ![(33238088795071/100000000000000 : ℝ), (5989412434693/20000000000000 : ℝ), (18407424512979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525144859/1250000000 : ℝ)|^4815 ≤ (33238088795071/100000000000000 : ℝ)^3791
        have hw : |(525144859/1250000000 : ℝ)|=(525144859/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3870056571/10000000000 : ℝ)|^4815 ≤ (5989412434693/20000000000000 : ℝ)^3791
        have hw : |(3870056571/10000000000 : ℝ)|=(3870056571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1138299043/2500000000 : ℝ)|^4815 ≤ (18407424512979/50000000000000 : ℝ)^3791
        have hw : |(1138299043/2500000000 : ℝ)|=(1138299043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_4 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1669750181/10000000000 : ℝ)*x 0 + (5184184773/10000000000 : ℝ)*x 1 + (1363260973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1669750181/10000000000 : ℝ)^4815 ≤ (10296253628793/100000000000000 : ℝ)^3791 := by
    have hnat : (1669750181 : ℕ)^4815*100000000000000^3791 ≤ 10296253628793^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669750181 10000000000 10296253628793 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184184773/10000000000 : ℝ)^4815 ≤ (21706102081559/50000000000000 : ℝ)^3791 := by
    have hnat : (5184184773 : ℕ)^4815*50000000000000^3791 ≤ 21706102081559^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184184773 10000000000 21706102081559 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1363260973/2500000000 : ℝ)^4815 ≤ (11572885548347/25000000000000 : ℝ)^3791 := by
    have hnat : (1363260973 : ℕ)^4815*25000000000000^3791 ≤ 11572885548347^3791*2500000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363260973 2500000000 11572885548347 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1669750181/10000000000 : ℝ), (5184184773/10000000000 : ℝ), (1363260973/2500000000 : ℝ)] ![(10296253628793/100000000000000 : ℝ), (21706102081559/50000000000000 : ℝ), (11572885548347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1669750181/10000000000 : ℝ)|^4815 ≤ (10296253628793/100000000000000 : ℝ)^3791
        have hw : |(-1669750181/10000000000 : ℝ)|=(1669750181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184184773/10000000000 : ℝ)|^4815 ≤ (21706102081559/50000000000000 : ℝ)^3791
        have hw : |(5184184773/10000000000 : ℝ)|=(5184184773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1363260973/2500000000 : ℝ)|^4815 ≤ (11572885548347/25000000000000 : ℝ)^3791
        have hw : |(1363260973/2500000000 : ℝ)|=(1363260973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_5 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278873233/10000000000 : ℝ)*x 0 + (-769722881/5000000000 : ℝ)*x 1 + (2726522017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278873233/10000000000 : ℝ)^4815 ≤ (44421773632949/100000000000000 : ℝ)^3791 := by
    have hnat : (5278873233 : ℕ)^4815*100000000000000^3791 ≤ 44421773632949^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278873233 10000000000 44421773632949 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769722881/5000000000 : ℝ)^4815 ≤ (9286682629487/100000000000000 : ℝ)^3791 := by
    have hnat : (769722881 : ℕ)^4815*100000000000000^3791 ≤ 9286682629487^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769722881 5000000000 9286682629487 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726522017/5000000000 : ℝ)^4815 ≤ (46291543724453/100000000000000 : ℝ)^3791 := by
    have hnat : (2726522017 : ℕ)^4815*100000000000000^3791 ≤ 46291543724453^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726522017 5000000000 46291543724453 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278873233/10000000000 : ℝ), (-769722881/5000000000 : ℝ), (2726522017/5000000000 : ℝ)] ![(44421773632949/100000000000000 : ℝ), (9286682629487/100000000000000 : ℝ), (46291543724453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278873233/10000000000 : ℝ)|^4815 ≤ (44421773632949/100000000000000 : ℝ)^3791
        have hw : |(5278873233/10000000000 : ℝ)|=(5278873233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-769722881/5000000000 : ℝ)|^4815 ≤ (9286682629487/100000000000000 : ℝ)^3791
        have hw : |(-769722881/5000000000 : ℝ)|=(769722881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726522017/5000000000 : ℝ)|^4815 ≤ (46291543724453/100000000000000 : ℝ)^3791
        have hw : |(2726522017/5000000000 : ℝ)|=(2726522017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_6 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278873347/10000000000 : ℝ)*x 0 + (2726521983/5000000000 : ℝ)*x 1 + (-769722849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278873347/10000000000 : ℝ)^4815 ≤ (44421774851383/100000000000000 : ℝ)^3791 := by
    have hnat : (5278873347 : ℕ)^4815*100000000000000^3791 ≤ 44421774851383^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278873347 10000000000 44421774851383 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726521983/5000000000 : ℝ)^4815 ≤ (46291542991267/100000000000000 : ℝ)^3791 := by
    have hnat : (2726521983 : ℕ)^4815*100000000000000^3791 ≤ 46291542991267^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726521983 5000000000 46291542991267 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769722849/5000000000 : ℝ)^4815 ≤ (9286682139123/100000000000000 : ℝ)^3791 := by
    have hnat : (769722849 : ℕ)^4815*100000000000000^3791 ≤ 9286682139123^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769722849 5000000000 9286682139123 100000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278873347/10000000000 : ℝ), (2726521983/5000000000 : ℝ), (-769722849/5000000000 : ℝ)] ![(44421774851383/100000000000000 : ℝ), (46291542991267/100000000000000 : ℝ), (9286682139123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278873347/10000000000 : ℝ)|^4815 ≤ (44421774851383/100000000000000 : ℝ)^3791
        have hw : |(5278873347/10000000000 : ℝ)|=(5278873347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726521983/5000000000 : ℝ)|^4815 ≤ (46291542991267/100000000000000 : ℝ)^3791
        have hw : |(2726521983/5000000000 : ℝ)|=(2726521983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-769722849/5000000000 : ℝ)|^4815 ≤ (9286682139123/100000000000000 : ℝ)^3791
        have hw : |(-769722849/5000000000 : ℝ)|=(769722849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1624_s5_7 (p : ℝ) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2100664553/5000000000 : ℝ)*x 0 + (909618099/2000000000 : ℝ)*x 1 + (3875215643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100664553/5000000000 : ℝ)^4815 ≤ (16619899716557/50000000000000 : ℝ)^3791 := by
    have hnat : (2100664553 : ℕ)^4815*50000000000000^3791 ≤ 16619899716557^3791*5000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100664553 5000000000 16619899716557 50000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909618099/2000000000 : ℝ)^4815 ≤ (7352484846913/20000000000000 : ℝ)^3791 := by
    have hnat : (909618099 : ℕ)^4815*20000000000000^3791 ≤ 7352484846913^3791*2000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909618099 2000000000 7352484846913 20000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3875215643/10000000000 : ℝ)^4815 ≤ (7499444081281/25000000000000 : ℝ)^3791 := by
    have hnat : (3875215643 : ℕ)^4815*25000000000000^3791 ≤ 7499444081281^3791*10000000000^4815 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875215643 10000000000 7499444081281 25000000000000 4815 3791 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4815/1024 : ℝ)) 4815 3791 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100664553/5000000000 : ℝ), (909618099/2000000000 : ℝ), (3875215643/10000000000 : ℝ)] ![(16619899716557/50000000000000 : ℝ), (7352484846913/20000000000000 : ℝ), (7499444081281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100664553/5000000000 : ℝ)|^4815 ≤ (16619899716557/50000000000000 : ℝ)^3791
        have hw : |(2100664553/5000000000 : ℝ)|=(2100664553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(909618099/2000000000 : ℝ)|^4815 ≤ (7352484846913/20000000000000 : ℝ)^3791
        have hw : |(909618099/2000000000 : ℝ)|=(909618099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3875215643/10000000000 : ℝ)|^4815 ≤ (7499444081281/25000000000000 : ℝ)^3791
        have hw : |(3875215643/10000000000 : ℝ)|=(3875215643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1624_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2631/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4079/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10523/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10523/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10523/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16317/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10523/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10523/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16317/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10523/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10523/100000 : ℝ) ^ (4811/1024 : ℝ) ≤ (509102080489573/20000000000000000000 : ℝ) := by
    have hpowers : (10523/100000 : ℝ)^4811 ≤ (509102080489573/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10523 : ℕ)^4811*20000000000000000000^1024 ≤ 509102080489573^1024*100000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10523 100000 509102080489573 20000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10523/100000 : ℝ)) (X := (509102080489573/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16317/100000 : ℝ) ^ (4811/1024 : ℝ) ≤ (19989112135508791/100000000000000000000 : ℝ) := by
    have hpowers : (16317/100000 : ℝ)^4811 ≤ (19989112135508791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16317 : ℕ)^4811*100000000000000000000^1024 ≤ 19989112135508791^1024*100000^4811 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16317 100000 19989112135508791 100000000000000000000 4811 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16317/100000 : ℝ)) (X := (19989112135508791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000509102080489573/10000000000000000000 : ℝ) ≤ (1000010835794741/1000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (10000509102080489573/10000000000000000000 : ℝ)^1024 ≤ (1000010835794741/1000000000000000 : ℝ)^4811 := by
      have hnat : (10000509102080489573 : ℕ)^1024*1000000000000000^4811 ≤ 1000010835794741^4811*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000509102080489573 10000000000000000000 1000010835794741 1000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000010835794741/1000000000000000 : ℝ)) (X := (10000509102080489573/10000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251408413908622291/6250000000000000000 : ℝ) ≤ (10000479596906367/10000000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (6251408413908622291/6250000000000000000 : ℝ)^1024 ≤ (10000479596906367/10000000000000000 : ℝ)^4811 := by
      have hnat : (6251408413908622291 : ℕ)^1024*10000000000000000^4811 ≤ 10000479596906367^4811*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251408413908622291 6250000000000000000 10000479596906367 10000000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000479596906367/10000000000000000 : ℝ)) (X := (6251408413908622291/6250000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019989112135508791/50000000000000000000 : ℝ) ≤ (2500212708966331/2500000000000000 : ℝ) ^ (4811/1024 : ℝ) := by
    have hpowers : (50019989112135508791/50000000000000000000 : ℝ)^1024 ≤ (2500212708966331/2500000000000000 : ℝ)^4811 := by
      have hnat : (50019989112135508791 : ℕ)^1024*2500000000000000^4811 ≤ 2500212708966331^4811*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019989112135508791 50000000000000000000 2500212708966331 2500000000000000 1024 4811 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500212708966331/2500000000000000 : ℝ)) (X := (50019989112135508791/50000000000000000000 : ℝ)) (by norm_num) 4811 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(509102080489573/20000000000000000000 : ℝ) ≤ ((28966407365408542259/28970000000000000000 : ℝ)+2*(371238958957/579400000000000 : ℝ)*(10523/100000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (28966407365408542259/28970000000000000000 : ℝ)+2*(371238958957/579400000000000 : ℝ)*(10523/100000 : ℝ)=(1000010835794741/1000000000000000 : ℝ) by norm_num, show 1+2*(509102080489573/20000000000000000000 : ℝ)=(10000509102080489573/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19989112135508791/100000000000000000000 : ℝ)+(509102080489573/20000000000000000000 : ℝ) ≤ ((28966407365408542259/28970000000000000000 : ℝ)+(371238958957/579400000000000 : ℝ)*((16317/100000 : ℝ)+(10523/100000 : ℝ)))^(4811/1024 : ℝ) := by
    rw [show (28966407365408542259/28970000000000000000 : ℝ)+(371238958957/579400000000000 : ℝ)*((16317/100000 : ℝ)+(10523/100000 : ℝ))=(10000479596906367/10000000000000000 : ℝ) by norm_num, show 1+(19989112135508791/100000000000000000000 : ℝ)+(509102080489573/20000000000000000000 : ℝ)=(6251408413908622291/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19989112135508791/100000000000000000000 : ℝ) ≤ ((28966407365408542259/28970000000000000000 : ℝ)+2*(371238958957/579400000000000 : ℝ)*(16317/100000 : ℝ))^(4811/1024 : ℝ) := by
    rw [show (28966407365408542259/28970000000000000000 : ℝ)+2*(371238958957/579400000000000 : ℝ)*(16317/100000 : ℝ)=(2500212708966331/2500000000000000 : ℝ) by norm_num, show 1+2*(19989112135508791/100000000000000000000 : ℝ)=(50019989112135508791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28966407365408542259/28970000000000000000 : ℝ)*(X 1 0+X 2 0)+(371238958957/579400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (10523/100000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (28966407365408542259/28970000000000000000 : ℝ)) (alpha := (371238958957/579400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28966407365408542259/28970000000000000000 : ℝ)*(X 0 1+X 2 1)+(371238958957/579400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (10523/100000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (28966407365408542259/28970000000000000000 : ℝ)) (alpha := (371238958957/579400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28966407365408542259/28970000000000000000 : ℝ)*(X 0 2+X 1 2)+(371238958957/579400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4811/1024 : ℝ)) (lo := (10523/100000 : ℝ)) (hi := (16317/100000 : ℝ)) (c := (28966407365408542259/28970000000000000000 : ℝ)) (alpha := (371238958957/579400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1669682319/10000000000 : ℝ)*X 0 0+(2727552753/5000000000 : ℝ)*X 0 1+(5182144567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675767907/5000000000 : ℝ)*X 1 0+(-905172523/5000000000 : ℝ)*X 1 1+(2591072363/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351535839/10000000000 : ℝ)*X 2 0+(1036428971/2000000000 : ℝ)*X 2 1+(-905172421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((525144859/1250000000 : ℝ)*X 0 0+(3870056571/10000000000 : ℝ)*X 0 1+(1138299043/2500000000 : ℝ)*X 0 2+(525144859/1250000000 : ℝ)*X 1 0+(3870056571/10000000000 : ℝ)*X 1 1+(1138299043/2500000000 : ℝ)*X 1 2+(525144859/1250000000 : ℝ)*X 2 0+(3870056571/10000000000 : ℝ)*X 2 1+(1138299043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1669750181/10000000000 : ℝ)*X 0 0+(5184184773/10000000000 : ℝ)*X 0 1+(1363260973/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278873233/10000000000 : ℝ)*X 1 0+(-769722881/5000000000 : ℝ)*X 1 1+(2726522017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278873347/10000000000 : ℝ)*X 2 0+(2726521983/5000000000 : ℝ)*X 2 1+(-769722849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2100664553/5000000000 : ℝ)*X 0 0+(909618099/2000000000 : ℝ)*X 0 1+(3875215643/10000000000 : ℝ)*X 0 2+(2100664553/5000000000 : ℝ)*X 1 0+(909618099/2000000000 : ℝ)*X 1 1+(3875215643/10000000000 : ℝ)*X 1 2+(2100664553/5000000000 : ℝ)*X 2 0+(909618099/2000000000 : ℝ)*X 2 1+(3875215643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1624_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11990613162715577093619266667/1448500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (629730361/50000000000000 : ℝ)*(base19) + (121683311/10000000000000 : ℝ)*(base23) + (31971233/100000000000000 : ℝ)*(lower2) + (93514631/100000000000000 : ℝ)*(upper3) + (52388917/25000000000000 : ℝ)*(upper5) + (2563705850001571/100000000000000 : ℝ)*(major0) + (2563705850001571/100000000000000 : ℝ)*(major1) + (2563705850001571/100000000000000 : ℝ)*(major2) + (9158863377089/250000000000 : ℝ)*(sp0) + (1831782594366799/50000000000000 : ℝ)*(sp1) + (366356523136121/10000000000000 : ℝ)*(sp2) + (292767522841143/20000000000000 : ℝ)*(sp3) + (21097358721/100000000000000 : ℝ)*(sp4) + (1840417843/25000000000000 : ℝ)*(sp7) + (1463844975877087/100000000000000 : ℝ)*(f.failure) + (45794580602429/1250000000000 : ℝ)*(f.sum) + (250866820362777/28970000000000000000000000000 : ℝ)*base65 + (44581253738143761111/2897000000000000000000000000000000 : ℝ)*base68 + (43872882687633761111/2897000000000000000000000000000000 : ℝ)*base70 + (18330680228505761111/2897000000000000000000000000000000 : ℝ)*base72 + (34394537784643/28970000000000000000000000000 : ℝ)*base74 + (29858751843585761111/2897000000000000000000000000000000 : ℝ)*base76 + (1753275138548238889/2897000000000000000000000000000000 : ℝ)*base77 + (2175440889407238889/2897000000000000000000000000000000 : ℝ)*base79 + (39045945311873/28970000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7248869/2000000000000000000000 : ℝ)*base90 + (7248869/2000000000000000000000 : ℝ)*base92 + (7248869/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1347850210249722078482130237/362125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1734391/400000000000 : ℝ)*(base19) + (139346429/20000000000000 : ℝ)*(base23) + (33122939/25000000000000 : ℝ)*(lower1) + (58739443/50000000000000 : ℝ)*(upper3) + (16305983/25000000000000 : ℝ)*(lower4) + (20167697/100000000000000 : ℝ)*(upper5) + (1301392905831981/50000000000000 : ℝ)*(major0) + (1301392905831981/50000000000000 : ℝ)*(major1) + (1301392905831981/50000000000000 : ℝ)*(major2) + (134526439/3125000000000 : ℝ)*(sp2) + (185970616940283/5000000000000 : ℝ)*(sp4) + (371941190520791/10000000000000 : ℝ)*(sp5) + (929851834306867/25000000000000 : ℝ)*(sp6) + (297231832090731/20000000000000 : ℝ)*(sp7) + (297231832090731/20000000000000 : ℝ)*(f.failure) + (185970616940283/5000000000000 : ℝ)*(f.sum) + (110525492191633/14485000000000000000000000000 : ℝ)*base66 + (23731772986340535079/1448500000000000000000000000000000 : ℝ)*base67 + (9053184165439464921/1448500000000000000000000000000000 : ℝ)*base70 + (48211935446826964921/1448500000000000000000000000000000 : ℝ)*base72 + (4053473398951/1810625000000000000000000000 : ℝ)*base74 + (21100474864109464921/1448500000000000000000000000000000 : ℝ)*base76 + (18593205366969964921/1448500000000000000000000000000000 : ℝ)*base78 + (21430901249337464921/1448500000000000000000000000000000 : ℝ)*base80 + (1633915868287/905312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3916503/400000000000000000000 : ℝ)*base89 + (3916503/400000000000000000000 : ℝ)*base91 + (3916503/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1624_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2631/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1624_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1624_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2631/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1624_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1624_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1624_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4811/1024 : ℝ) ≤ p) (hpb : p ≤ (4815/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35027013/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16437/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2083/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2631/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4079/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1624_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
