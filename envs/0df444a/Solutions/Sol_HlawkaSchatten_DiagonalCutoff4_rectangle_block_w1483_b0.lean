-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1483_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:02.196407+00:00
-- url     : https://prove2.me/submissions/cb40e8f3-a792-4c77-8612-93d3371dd4ad

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
theorem support_rectangle_w1483_s0_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-858514391/5000000000 : ℝ)*x 0 + (5935508933/10000000000 : ℝ)*x 1 + (4842718621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858514391/5000000000 : ℝ)^4463 ≤ (5080356662157/50000000000000 : ℝ)^3439 := by
    have hnat : (858514391 : ℕ)^4463*50000000000000^3439 ≤ 5080356662157^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858514391 5000000000 5080356662157 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5935508933/10000000000 : ℝ)^4463 ≤ (12704061670347/25000000000000 : ℝ)^3439 := by
    have hnat : (5935508933 : ℕ)^4463*25000000000000^3439 ≤ 12704061670347^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5935508933 10000000000 12704061670347 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4842718621/10000000000 : ℝ)^4463 ≤ (9755759995773/25000000000000 : ℝ)^3439 := by
    have hnat : (4842718621 : ℕ)^4463*25000000000000^3439 ≤ 9755759995773^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4842718621 10000000000 9755759995773 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-858514391/5000000000 : ℝ), (5935508933/10000000000 : ℝ), (4842718621/10000000000 : ℝ)] ![(5080356662157/50000000000000 : ℝ), (12704061670347/25000000000000 : ℝ), (9755759995773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-858514391/5000000000 : ℝ)|^4463 ≤ (5080356662157/50000000000000 : ℝ)^3439
        have hw : |(-858514391/5000000000 : ℝ)|=(858514391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5935508933/10000000000 : ℝ)|^4463 ≤ (12704061670347/25000000000000 : ℝ)^3439
        have hw : |(5935508933/10000000000 : ℝ)|=(5935508933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4842718621/10000000000 : ℝ)|^4463 ≤ (9755759995773/25000000000000 : ℝ)^3439
        have hw : |(4842718621/10000000000 : ℝ)|=(4842718621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5484317287/10000000000 : ℝ)*x 0 + (-1165944439/5000000000 : ℝ)*x 1 + (968543731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5484317287/10000000000 : ℝ)^4463 ≤ (11465248264269/25000000000000 : ℝ)^3439 := by
    have hnat : (5484317287 : ℕ)^4463*25000000000000^3439 ≤ 11465248264269^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484317287 10000000000 11465248264269 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165944439/5000000000 : ℝ)^4463 ≤ (7557983289181/50000000000000 : ℝ)^3439 := by
    have hnat : (1165944439 : ℕ)^4463*50000000000000^3439 ≤ 7557983289181^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165944439 5000000000 7557983289181 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968543731/2000000000 : ℝ)^4463 ≤ (19511520169323/50000000000000 : ℝ)^3439 := by
    have hnat : (968543731 : ℕ)^4463*50000000000000^3439 ≤ 19511520169323^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968543731 2000000000 19511520169323 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5484317287/10000000000 : ℝ), (-1165944439/5000000000 : ℝ), (968543731/2000000000 : ℝ)] ![(11465248264269/25000000000000 : ℝ), (7557983289181/50000000000000 : ℝ), (19511520169323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5484317287/10000000000 : ℝ)|^4463 ≤ (11465248264269/25000000000000 : ℝ)^3439
        have hw : |(5484317287/10000000000 : ℝ)|=(5484317287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1165944439/5000000000 : ℝ)|^4463 ≤ (7557983289181/50000000000000 : ℝ)^3439
        have hw : |(-1165944439/5000000000 : ℝ)|=(1165944439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968543731/2000000000 : ℝ)|^4463 ≤ (19511520169323/50000000000000 : ℝ)^3439
        have hw : |(968543731/2000000000 : ℝ)|=(968543731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (685539649/1250000000 : ℝ)*x 0 + (1210679677/2500000000 : ℝ)*x 1 + (-291486117/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (685539649/1250000000 : ℝ)^4463 ≤ (22930496013061/50000000000000 : ℝ)^3439 := by
    have hnat : (685539649 : ℕ)^4463*50000000000000^3439 ≤ 22930496013061^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685539649 1250000000 22930496013061 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210679677/2500000000 : ℝ)^4463 ≤ (9755760223223/25000000000000 : ℝ)^3439 := by
    have hnat : (1210679677 : ℕ)^4463*25000000000000^3439 ≤ 9755760223223^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210679677 2500000000 9755760223223 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291486117/1250000000 : ℝ)^4463 ≤ (3778991766571/25000000000000 : ℝ)^3439 := by
    have hnat : (291486117 : ℕ)^4463*25000000000000^3439 ≤ 3778991766571^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291486117 1250000000 3778991766571 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(685539649/1250000000 : ℝ), (1210679677/2500000000 : ℝ), (-291486117/1250000000 : ℝ)] ![(22930496013061/50000000000000 : ℝ), (9755760223223/25000000000000 : ℝ), (3778991766571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(685539649/1250000000 : ℝ)|^4463 ≤ (22930496013061/50000000000000 : ℝ)^3439
        have hw : |(685539649/1250000000 : ℝ)|=(685539649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1210679677/2500000000 : ℝ)|^4463 ≤ (9755760223223/25000000000000 : ℝ)^3439
        have hw : |(1210679677/2500000000 : ℝ)|=(1210679677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-291486117/1250000000 : ℝ)|^4463 ≤ (3778991766571/25000000000000 : ℝ)^3439
        have hw : |(-291486117/1250000000 : ℝ)|=(291486117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038264341/2500000000 : ℝ)*x 0 + (386427389/1250000000 : ℝ)*x 1 + (2759431081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038264341/2500000000 : ℝ)^4463 ≤ (1278771012697/4000000000000 : ℝ)^3439 := by
    have hnat : (1038264341 : ℕ)^4463*4000000000000^3439 ≤ 1278771012697^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038264341 2500000000 1278771012697 4000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386427389/1250000000 : ℝ)^4463 ≤ (10897247287899/50000000000000 : ℝ)^3439 := by
    have hnat : (386427389 : ℕ)^4463*50000000000000^3439 ≤ 10897247287899^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386427389 1250000000 10897247287899 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759431081/5000000000 : ℝ)^4463 ≤ (46236230096101/100000000000000 : ℝ)^3439 := by
    have hnat : (2759431081 : ℕ)^4463*100000000000000^3439 ≤ 46236230096101^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759431081 5000000000 46236230096101 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038264341/2500000000 : ℝ), (386427389/1250000000 : ℝ), (2759431081/5000000000 : ℝ)] ![(1278771012697/4000000000000 : ℝ), (10897247287899/50000000000000 : ℝ), (46236230096101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038264341/2500000000 : ℝ)|^4463 ≤ (1278771012697/4000000000000 : ℝ)^3439
        have hw : |(1038264341/2500000000 : ℝ)|=(1038264341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386427389/1250000000 : ℝ)|^4463 ≤ (10897247287899/50000000000000 : ℝ)^3439
        have hw : |(386427389/1250000000 : ℝ)|=(386427389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759431081/5000000000 : ℝ)|^4463 ≤ (46236230096101/100000000000000 : ℝ)^3439
        have hw : |(2759431081/5000000000 : ℝ)|=(2759431081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-860402423/5000000000 : ℝ)*x 0 + (2435369639/5000000000 : ℝ)*x 1 + (5906480859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860402423/5000000000 : ℝ)^4463 ≤ (10189721657773/100000000000000 : ℝ)^3439 := by
    have hnat : (860402423 : ℕ)^4463*100000000000000^3439 ≤ 10189721657773^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860402423 5000000000 10189721657773 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2435369639/5000000000 : ℝ)^4463 ≤ (9829079302689/25000000000000 : ℝ)^3439 := by
    have hnat : (2435369639 : ℕ)^4463*25000000000000^3439 ≤ 9829079302689^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435369639 5000000000 9829079302689 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5906480859/10000000000 : ℝ)^4463 ≤ (6311745138897/12500000000000 : ℝ)^3439 := by
    have hnat : (5906480859 : ℕ)^4463*12500000000000^3439 ≤ 6311745138897^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5906480859 10000000000 6311745138897 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-860402423/5000000000 : ℝ), (2435369639/5000000000 : ℝ), (5906480859/10000000000 : ℝ)] ![(10189721657773/100000000000000 : ℝ), (9829079302689/25000000000000 : ℝ), (6311745138897/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-860402423/5000000000 : ℝ)|^4463 ≤ (10189721657773/100000000000000 : ℝ)^3439
        have hw : |(-860402423/5000000000 : ℝ)|=(860402423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2435369639/5000000000 : ℝ)|^4463 ≤ (9829079302689/25000000000000 : ℝ)^3439
        have hw : |(2435369639/5000000000 : ℝ)|=(2435369639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5906480859/10000000000 : ℝ)|^4463 ≤ (6311745138897/12500000000000 : ℝ)^3439
        have hw : |(5906480859/10000000000 : ℝ)|=(5906480859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648239491/1250000000 : ℝ)*x 0 + (-253625289/2000000000 : ℝ)*x 1 + (2953240427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648239491/1250000000 : ℝ)^4463 ≤ (2665579520687/6250000000000 : ℝ)^3439 := by
    have hnat : (648239491 : ℕ)^4463*6250000000000^3439 ≤ 2665579520687^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648239491 1250000000 2665579520687 6250000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253625289/2000000000 : ℝ)^4463 ≤ (3428383300349/50000000000000 : ℝ)^3439 := by
    have hnat : (253625289 : ℕ)^4463*50000000000000^3439 ≤ 3428383300349^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253625289 2000000000 3428383300349 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2953240427/5000000000 : ℝ)^4463 ≤ (50493961055703/100000000000000 : ℝ)^3439 := by
    have hnat : (2953240427 : ℕ)^4463*100000000000000^3439 ≤ 50493961055703^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953240427 5000000000 50493961055703 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648239491/1250000000 : ℝ), (-253625289/2000000000 : ℝ), (2953240427/5000000000 : ℝ)] ![(2665579520687/6250000000000 : ℝ), (3428383300349/50000000000000 : ℝ), (50493961055703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648239491/1250000000 : ℝ)|^4463 ≤ (2665579520687/6250000000000 : ℝ)^3439
        have hw : |(648239491/1250000000 : ℝ)|=(648239491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253625289/2000000000 : ℝ)|^4463 ≤ (3428383300349/50000000000000 : ℝ)^3439
        have hw : |(-253625289/2000000000 : ℝ)|=(253625289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2953240427/5000000000 : ℝ)|^4463 ≤ (50493961055703/100000000000000 : ℝ)^3439
        have hw : |(2953240427/5000000000 : ℝ)|=(2953240427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037183161/2000000000 : ℝ)*x 0 + (5906480839/10000000000 : ℝ)*x 1 + (-19814479/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037183161/2000000000 : ℝ)^4463 ≤ (4264927101823/10000000000000 : ℝ)^3439 := by
    have hnat : (1037183161 : ℕ)^4463*10000000000000^3439 ≤ 4264927101823^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037183161 2000000000 4264927101823 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5906480839/10000000000 : ℝ)^4463 ≤ (50493960889287/100000000000000 : ℝ)^3439 := by
    have hnat : (5906480839 : ℕ)^4463*100000000000000^3439 ≤ 50493960889287^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5906480839 10000000000 50493960889287 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19814479/156250000 : ℝ)^4463 ≤ (1371353616257/20000000000000 : ℝ)^3439 := by
    have hnat : (19814479 : ℕ)^4463*20000000000000^3439 ≤ 1371353616257^3439*156250000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19814479 156250000 1371353616257 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037183161/2000000000 : ℝ), (5906480839/10000000000 : ℝ), (-19814479/156250000 : ℝ)] ![(4264927101823/10000000000000 : ℝ), (50493960889287/100000000000000 : ℝ), (1371353616257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037183161/2000000000 : ℝ)|^4463 ≤ (4264927101823/10000000000000 : ℝ)^3439
        have hw : |(1037183161/2000000000 : ℝ)|=(1037183161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5906480839/10000000000 : ℝ)|^4463 ≤ (50493960889287/100000000000000 : ℝ)^3439
        have hw : |(5906480839/10000000000 : ℝ)|=(5906480839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19814479/156250000 : ℝ)|^4463 ≤ (1371353616257/20000000000000 : ℝ)^3439
        have hw : |(-19814479/156250000 : ℝ)|=(19814479/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s0_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (832289153/2000000000 : ℝ)*x 0 + (5456618939/10000000000 : ℝ)*x 1 + (1577950039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (832289153/2000000000 : ℝ)^4463 ≤ (4006637436173/12500000000000 : ℝ)^3439 := by
    have hnat : (832289153 : ℕ)^4463*12500000000000^3439 ≤ 4006637436173^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832289153 2000000000 4006637436173 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456618939/10000000000 : ℝ)^4463 ≤ (22780316424029/50000000000000 : ℝ)^3439 := by
    have hnat : (5456618939 : ℕ)^4463*50000000000000^3439 ≤ 22780316424029^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456618939 10000000000 22780316424029 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577950039/5000000000 : ℝ)^4463 ≤ (2238626765339/10000000000000 : ℝ)^3439 := by
    have hnat : (1577950039 : ℕ)^4463*10000000000000^3439 ≤ 2238626765339^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577950039 5000000000 2238626765339 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(832289153/2000000000 : ℝ), (5456618939/10000000000 : ℝ), (1577950039/5000000000 : ℝ)] ![(4006637436173/12500000000000 : ℝ), (22780316424029/50000000000000 : ℝ), (2238626765339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(832289153/2000000000 : ℝ)|^4463 ≤ (4006637436173/12500000000000 : ℝ)^3439
        have hw : |(832289153/2000000000 : ℝ)|=(832289153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456618939/10000000000 : ℝ)|^4463 ≤ (22780316424029/50000000000000 : ℝ)^3439
        have hw : |(5456618939/10000000000 : ℝ)|=(5456618939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577950039/5000000000 : ℝ)|^4463 ≤ (2238626765339/10000000000000 : ℝ)^3439
        have hw : |(1577950039/5000000000 : ℝ)|=(1577950039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1223/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5173/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4461/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4461 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4461*1^1024 ≤ 0^1024*1^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4461/1024 : ℝ) ≤ (1846699002335449831/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4461 ≤ (1846699002335449831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4461*100000000000000000000^1024 ≤ 1846699002335449831^1024*5^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1846699002335449831 100000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1846699002335449831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4461 := by
      have hnat : (1 : ℕ)^1024*1^4461 ≤ 1^4461*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101846699002335449831/100000000000000000000 : ℝ) ≤ (2510522931178631/2500000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (101846699002335449831/100000000000000000000 : ℝ)^1024 ≤ (2510522931178631/2500000000000000 : ℝ)^4461 := by
      have hnat : (101846699002335449831 : ℕ)^1024*2500000000000000^4461 ≤ 2510522931178631^4461*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101846699002335449831 100000000000000000000 2510522931178631 2500000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510522931178631/2500000000000000 : ℝ)) (X := (101846699002335449831/100000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51846699002335449831/50000000000000000000 : ℝ) ≤ (1260522931178631/1250000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (51846699002335449831/50000000000000000000 : ℝ)^1024 ≤ (1260522931178631/1250000000000000 : ℝ)^4461 := by
      have hnat : (51846699002335449831 : ℕ)^1024*1250000000000000^4461 ≤ 1260522931178631^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51846699002335449831 50000000000000000000 1260522931178631 1250000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260522931178631/1250000000000000 : ℝ)) (X := (51846699002335449831/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10522931178631/1000000000000000 : ℝ)*(0 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10522931178631/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1846699002335449831/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10522931178631/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10522931178631/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2510522931178631/2500000000000000 : ℝ) by norm_num, show 1+(1846699002335449831/100000000000000000000 : ℝ)+(0 : ℝ)=(101846699002335449831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1846699002335449831/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10522931178631/1000000000000000 : ℝ)*(2/5 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10522931178631/1000000000000000 : ℝ)*(2/5 : ℝ)=(1260522931178631/1250000000000000 : ℝ) by norm_num, show 1+2*(1846699002335449831/100000000000000000000 : ℝ)=(51846699002335449831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10522931178631/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10522931178631/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10522931178631/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10522931178631/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10522931178631/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10522931178631/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-858514391/5000000000 : ℝ)*X 0 0+(5935508933/10000000000 : ℝ)*X 0 1+(4842718621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5484317287/10000000000 : ℝ)*X 1 0+(-1165944439/5000000000 : ℝ)*X 1 1+(968543731/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((685539649/1250000000 : ℝ)*X 2 0+(1210679677/2500000000 : ℝ)*X 2 1+(-291486117/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1038264341/2500000000 : ℝ)*X 0 0+(386427389/1250000000 : ℝ)*X 0 1+(2759431081/5000000000 : ℝ)*X 0 2+(1038264341/2500000000 : ℝ)*X 1 0+(386427389/1250000000 : ℝ)*X 1 1+(2759431081/5000000000 : ℝ)*X 1 2+(1038264341/2500000000 : ℝ)*X 2 0+(386427389/1250000000 : ℝ)*X 2 1+(2759431081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-860402423/5000000000 : ℝ)*X 0 0+(2435369639/5000000000 : ℝ)*X 0 1+(5906480859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((648239491/1250000000 : ℝ)*X 1 0+(-253625289/2000000000 : ℝ)*X 1 1+(2953240427/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1037183161/2000000000 : ℝ)*X 2 0+(5906480839/10000000000 : ℝ)*X 2 1+(-19814479/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((832289153/2000000000 : ℝ)*X 0 0+(5456618939/10000000000 : ℝ)*X 0 1+(1577950039/5000000000 : ℝ)*X 0 2+(832289153/2000000000 : ℝ)*X 1 0+(5456618939/10000000000 : ℝ)*X 1 1+(1577950039/5000000000 : ℝ)*X 1 2+(832289153/2000000000 : ℝ)*X 2 0+(5456618939/10000000000 : ℝ)*X 2 1+(1577950039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36242919401289567695967/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19691897/50000000000000 : ℝ)*(base1) + (1288715987/100000000000000 : ℝ)*(base19) + (1272864581/100000000000000 : ℝ)*(base23) + (173593833/100000000000000 : ℝ)*(upper3) + (153045607/100000000000000 : ℝ)*(upper5) + (165882229504269/25000000000000 : ℝ)*(major0) + (165882229504269/25000000000000 : ℝ)*(major1) + (165882229504269/25000000000000 : ℝ)*(major2) + (183018606009437/20000000000000 : ℝ)*(sp0) + (915096167908967/100000000000000 : ℝ)*(sp1) + (228774045940093/25000000000000 : ℝ)*(sp2) + (411958050672323/100000000000000 : ℝ)*(sp3) + (4465961563/100000000000000 : ℝ)*(sp4) + (2096057507/100000000000000 : ℝ)*(sp7) + (411960186113623/100000000000000 : ℝ)*(f.failure) + (915097456624953/100000000000000 : ℝ)*(f.sum) + (14125627161761/12500000000000000000000000000 : ℝ)*base66 + (70127418124261/25000000000000000000000000000 : ℝ)*base68 + (156981043274261/25000000000000000000000000000 : ℝ)*base70 + (60772907824261/25000000000000000000000000000 : ℝ)*base72 + (7466100788239/12500000000000000000000000000 : ℝ)*base73 + (222864165349261/25000000000000000000000000000 : ℝ)*base76 + (14039519800739/25000000000000000000000000000 : ℝ)*base77 + (21070975450739/25000000000000000000000000000 : ℝ)*base79 + (49032529924261/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (11137079/10000000000000000000000 : ℝ)*base89 + (11137079/10000000000000000000000 : ℝ)*base91 + (11137079/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76002313390497353643171/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (700297507/50000000000000 : ℝ)*(base19) + (1379972559/100000000000000 : ℝ)*(base23) + (113855937/100000000000000 : ℝ)*(base32) + (202033257/100000000000000 : ℝ)*(upper3) + (66602943/50000000000000 : ℝ)*(upper5) + (700069015780947/100000000000000 : ℝ)*(major0) + (700069015780947/100000000000000 : ℝ)*(major1) + (700069015780947/100000000000000 : ℝ)*(major2) + (697186361/20000000000000 : ℝ)*(sp1) + (881376373/25000000000000 : ℝ)*(sp2) + (965491268351241/100000000000000 : ℝ)*(sp4) + (482743190912211/50000000000000 : ℝ)*(sp5) + (96548636287319/10000000000000 : ℝ)*(sp6) + (217323223340939/50000000000000 : ℝ)*(sp7) + (86929312107563/20000000000000 : ℝ)*(f.failure) + (965491268351241/100000000000000 : ℝ)*(f.sum) + (33368015856443/50000000000000000000000000000 : ℝ)*base66 + (59409520656443/100000000000000000000000000000 : ℝ)*base68 + (662924626956443/100000000000000000000000000000 : ℝ)*base70 + (27161708756443/100000000000000000000000000000 : ℝ)*base72 + (6159480243557/50000000000000000000000000000 : ℝ)*base73 + (343778891356443/100000000000000000000000000000 : ℝ)*base76 + (255559685056443/100000000000000000000000000000 : ℝ)*base78 + (174230195456443/100000000000000000000000000000 : ℝ)*base80 + (156876243256443/50000000000000000000000000000 : ℝ)*base82 + (7522699/2000000000000000000000 : ℝ)*base89 + (7522699/2000000000000000000000 : ℝ)*base91 + (7522699/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1483_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1223/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5173/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1483_s1_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878610117/10000000000 : ℝ)*x 0 + (5590573681/10000000000 : ℝ)*x 1 + (5083927679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878610117/10000000000 : ℝ)^4463 ≤ (11418618159013/100000000000000 : ℝ)^3439 := by
    have hnat : (1878610117 : ℕ)^4463*100000000000000^3439 ≤ 11418618159013^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878610117 10000000000 11418618159013 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5590573681/10000000000 : ℝ)^4463 ≤ (23508707023891/50000000000000 : ℝ)^3439 := by
    have hnat : (5590573681 : ℕ)^4463*50000000000000^3439 ≤ 23508707023891^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590573681 10000000000 23508707023891 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083927679/10000000000 : ℝ)^4463 ≤ (8312793555247/20000000000000 : ℝ)^3439 := by
    have hnat : (5083927679 : ℕ)^4463*20000000000000^3439 ≤ 8312793555247^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083927679 10000000000 8312793555247 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878610117/10000000000 : ℝ), (5590573681/10000000000 : ℝ), (5083927679/10000000000 : ℝ)] ![(11418618159013/100000000000000 : ℝ), (23508707023891/50000000000000 : ℝ), (8312793555247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878610117/10000000000 : ℝ)|^4463 ≤ (11418618159013/100000000000000 : ℝ)^3439
        have hw : |(-1878610117/10000000000 : ℝ)|=(1878610117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5590573681/10000000000 : ℝ)|^4463 ≤ (23508707023891/50000000000000 : ℝ)^3439
        have hw : |(5590573681/10000000000 : ℝ)|=(5590573681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083927679/10000000000 : ℝ)|^4463 ≤ (8312793555247/20000000000000 : ℝ)^3439
        have hw : |(5083927679/10000000000 : ℝ)|=(5083927679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391997267/10000000000 : ℝ)*x 0 + (-2146399483/10000000000 : ℝ)*x 1 + (5083928387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391997267/10000000000 : ℝ)^4463 ≤ (44861643627053/100000000000000 : ℝ)^3439 := by
    have hnat : (5391997267 : ℕ)^4463*100000000000000^3439 ≤ 44861643627053^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391997267 10000000000 44861643627053 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146399483/10000000000 : ℝ)^4463 ≤ (1357438107411/10000000000000 : ℝ)^3439 := by
    have hnat : (2146399483 : ℕ)^4463*10000000000000^3439 ≤ 1357438107411^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146399483 10000000000 1357438107411 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5083928387/10000000000 : ℝ)^4463 ≤ (41563975288063/100000000000000 : ℝ)^3439 := by
    have hnat : (5083928387 : ℕ)^4463*100000000000000^3439 ≤ 41563975288063^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083928387 10000000000 41563975288063 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391997267/10000000000 : ℝ), (-2146399483/10000000000 : ℝ), (5083928387/10000000000 : ℝ)] ![(44861643627053/100000000000000 : ℝ), (1357438107411/10000000000000 : ℝ), (41563975288063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391997267/10000000000 : ℝ)|^4463 ≤ (44861643627053/100000000000000 : ℝ)^3439
        have hw : |(5391997267/10000000000 : ℝ)|=(5391997267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146399483/10000000000 : ℝ)|^4463 ≤ (1357438107411/10000000000000 : ℝ)^3439
        have hw : |(-2146399483/10000000000 : ℝ)|=(2146399483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5083928387/10000000000 : ℝ)|^4463 ≤ (41563975288063/100000000000000 : ℝ)^3439
        have hw : |(5083928387/10000000000 : ℝ)|=(5083928387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336999873/625000000 : ℝ)*x 0 + (2541964049/5000000000 : ℝ)*x 1 + (-429279787/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336999873/625000000 : ℝ)^4463 ≤ (44861651196049/100000000000000 : ℝ)^3439 := by
    have hnat : (336999873 : ℕ)^4463*100000000000000^3439 ≤ 44861651196049^3439*625000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336999873 625000000 44861651196049 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541964049/5000000000 : ℝ)^4463 ≤ (20781986110897/50000000000000 : ℝ)^3439 := by
    have hnat : (2541964049 : ℕ)^4463*50000000000000^3439 ≤ 20781986110897^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541964049 5000000000 20781986110897 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429279787/2000000000 : ℝ)^4463 ≤ (1357437657647/10000000000000 : ℝ)^3439 := by
    have hnat : (429279787 : ℕ)^4463*10000000000000^3439 ≤ 1357437657647^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429279787 2000000000 1357437657647 10000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336999873/625000000 : ℝ), (2541964049/5000000000 : ℝ), (-429279787/2000000000 : ℝ)] ![(44861651196049/100000000000000 : ℝ), (20781986110897/50000000000000 : ℝ), (1357437657647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336999873/625000000 : ℝ)|^4463 ≤ (44861651196049/100000000000000 : ℝ)^3439
        have hw : |(336999873/625000000 : ℝ)|=(336999873/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541964049/5000000000 : ℝ)|^4463 ≤ (20781986110897/50000000000000 : ℝ)^3439
        have hw : |(2541964049/5000000000 : ℝ)|=(2541964049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429279787/2000000000 : ℝ)|^4463 ≤ (1357437657647/10000000000000 : ℝ)^3439
        have hw : |(-429279787/2000000000 : ℝ)|=(429279787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852034979/2000000000 : ℝ)*x 0 + (1864798913/5000000000 : ℝ)*x 1 + (2427511331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852034979/2000000000 : ℝ)^4463 ≤ (33043449472819/100000000000000 : ℝ)^3439 := by
    have hnat : (852034979 : ℕ)^4463*100000000000000^3439 ≤ 33043449472819^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852034979 2000000000 33043449472819 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864798913/5000000000 : ℝ)^4463 ≤ (27804792765649/100000000000000 : ℝ)^3439 := by
    have hnat : (1864798913 : ℕ)^4463*100000000000000^3439 ≤ 27804792765649^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864798913 5000000000 27804792765649 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2427511331/5000000000 : ℝ)^4463 ≤ (39151757749099/100000000000000 : ℝ)^3439 := by
    have hnat : (2427511331 : ℕ)^4463*100000000000000^3439 ≤ 39151757749099^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427511331 5000000000 39151757749099 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852034979/2000000000 : ℝ), (1864798913/5000000000 : ℝ), (2427511331/5000000000 : ℝ)] ![(33043449472819/100000000000000 : ℝ), (27804792765649/100000000000000 : ℝ), (39151757749099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852034979/2000000000 : ℝ)|^4463 ≤ (33043449472819/100000000000000 : ℝ)^3439
        have hw : |(852034979/2000000000 : ℝ)|=(852034979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1864798913/5000000000 : ℝ)|^4463 ≤ (27804792765649/100000000000000 : ℝ)^3439
        have hw : |(1864798913/5000000000 : ℝ)|=(1864798913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2427511331/5000000000 : ℝ)|^4463 ≤ (39151757749099/100000000000000 : ℝ)^3439
        have hw : |(2427511331/5000000000 : ℝ)|=(2427511331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375794487/2000000000 : ℝ)*x 0 + (5089831031/10000000000 : ℝ)*x 1 + (139614279/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375794487/2000000000 : ℝ)^4463 ≤ (11421476236403/100000000000000 : ℝ)^3439 := by
    have hnat : (375794487 : ℕ)^4463*100000000000000^3439 ≤ 11421476236403^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375794487 2000000000 11421476236403 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5089831031/10000000000 : ℝ)^4463 ≤ (41626612727963/100000000000000 : ℝ)^3439 := by
    have hnat : (5089831031 : ℕ)^4463*100000000000000^3439 ≤ 41626612727963^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5089831031 10000000000 41626612727963 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139614279/250000000 : ℝ)^4463 ≤ (9390382205739/20000000000000 : ℝ)^3439 := by
    have hnat : (139614279 : ℕ)^4463*20000000000000^3439 ≤ 9390382205739^3439*250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139614279 250000000 9390382205739 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375794487/2000000000 : ℝ), (5089831031/10000000000 : ℝ), (139614279/250000000 : ℝ)] ![(11421476236403/100000000000000 : ℝ), (41626612727963/100000000000000 : ℝ), (9390382205739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375794487/2000000000 : ℝ)|^4463 ≤ (11421476236403/100000000000000 : ℝ)^3439
        have hw : |(-375794487/2000000000 : ℝ)|=(375794487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5089831031/10000000000 : ℝ)|^4463 ≤ (41626612727963/100000000000000 : ℝ)^3439
        have hw : |(5089831031/10000000000 : ℝ)|=(5089831031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(139614279/250000000 : ℝ)|^4463 ≤ (9390382205739/20000000000000 : ℝ)^3439
        have hw : |(139614279/250000000 : ℝ)|=(139614279/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26295181/50000000 : ℝ)*x 0 + (-164575617/1000000000 : ℝ)*x 1 + (698071401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26295181/50000000 : ℝ)^4463 ≤ (1737252307337/4000000000000 : ℝ)^3439 := by
    have hnat : (26295181 : ℕ)^4463*4000000000000^3439 ≤ 1737252307337^3439*50000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26295181 50000000 1737252307337 4000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164575617/1000000000 : ℝ)^4463 ≤ (9616780758639/100000000000000 : ℝ)^3439 := by
    have hnat : (164575617 : ℕ)^4463*100000000000000^3439 ≤ 9616780758639^3439*1000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164575617 1000000000 9616780758639 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (698071401/1250000000 : ℝ)^4463 ≤ (9390382310483/20000000000000 : ℝ)^3439 := by
    have hnat : (698071401 : ℕ)^4463*20000000000000^3439 ≤ 9390382310483^3439*1250000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698071401 1250000000 9390382310483 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26295181/50000000 : ℝ), (-164575617/1000000000 : ℝ), (698071401/1250000000 : ℝ)] ![(1737252307337/4000000000000 : ℝ), (9616780758639/100000000000000 : ℝ), (9390382310483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26295181/50000000 : ℝ)|^4463 ≤ (1737252307337/4000000000000 : ℝ)^3439
        have hw : |(26295181/50000000 : ℝ)|=(26295181/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164575617/1000000000 : ℝ)|^4463 ≤ (9616780758639/100000000000000 : ℝ)^3439
        have hw : |(-164575617/1000000000 : ℝ)|=(164575617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(698071401/1250000000 : ℝ)|^4463 ≤ (9390382310483/20000000000000 : ℝ)^3439
        have hw : |(698071401/1250000000 : ℝ)|=(698071401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5259036207/10000000000 : ℝ)*x 0 + (5584571183/10000000000 : ℝ)*x 1 + (-329151239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5259036207/10000000000 : ℝ)^4463 ≤ (43431307758447/100000000000000 : ℝ)^3439 := by
    have hnat : (5259036207 : ℕ)^4463*100000000000000^3439 ≤ 43431307758447^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259036207 10000000000 43431307758447 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5584571183/10000000000 : ℝ)^4463 ≤ (11737977819911/25000000000000 : ℝ)^3439 := by
    have hnat : (5584571183 : ℕ)^4463*25000000000000^3439 ≤ 11737977819911^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5584571183 10000000000 11737977819911 25000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329151239/2000000000 : ℝ)^4463 ≤ (4808390474111/50000000000000 : ℝ)^3439 := by
    have hnat : (329151239 : ℕ)^4463*50000000000000^3439 ≤ 4808390474111^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329151239 2000000000 4808390474111 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5259036207/10000000000 : ℝ), (5584571183/10000000000 : ℝ), (-329151239/2000000000 : ℝ)] ![(43431307758447/100000000000000 : ℝ), (11737977819911/25000000000000 : ℝ), (4808390474111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5259036207/10000000000 : ℝ)|^4463 ≤ (43431307758447/100000000000000 : ℝ)^3439
        have hw : |(5259036207/10000000000 : ℝ)|=(5259036207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5584571183/10000000000 : ℝ)|^4463 ≤ (11737977819911/25000000000000 : ℝ)^3439
        have hw : |(5584571183/10000000000 : ℝ)|=(5584571183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329151239/2000000000 : ℝ)|^4463 ≤ (4808390474111/50000000000000 : ℝ)^3439
        have hw : |(-329151239/2000000000 : ℝ)|=(329151239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s1_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065245007/2500000000 : ℝ)*x 0 + (968382053/2000000000 : ℝ)*x 1 + (1871465439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065245007/2500000000 : ℝ)^4463 ≤ (16525777045007/50000000000000 : ℝ)^3439 := by
    have hnat : (1065245007 : ℕ)^4463*50000000000000^3439 ≤ 16525777045007^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065245007 2500000000 16525777045007 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968382053/2000000000 : ℝ)^4463 ≤ (19507293417797/50000000000000 : ℝ)^3439 := by
    have hnat : (968382053 : ℕ)^4463*50000000000000^3439 ≤ 19507293417797^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968382053 2000000000 19507293417797 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871465439/5000000000 : ℝ)^4463 ≤ (27933859058677/100000000000000 : ℝ)^3439 := by
    have hnat : (1871465439 : ℕ)^4463*100000000000000^3439 ≤ 27933859058677^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871465439 5000000000 27933859058677 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065245007/2500000000 : ℝ), (968382053/2000000000 : ℝ), (1871465439/5000000000 : ℝ)] ![(16525777045007/50000000000000 : ℝ), (19507293417797/50000000000000 : ℝ), (27933859058677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065245007/2500000000 : ℝ)|^4463 ≤ (16525777045007/50000000000000 : ℝ)^3439
        have hw : |(1065245007/2500000000 : ℝ)|=(1065245007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(968382053/2000000000 : ℝ)|^4463 ≤ (19507293417797/50000000000000 : ℝ)^3439
        have hw : |(968382053/2000000000 : ℝ)|=(968382053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1871465439/5000000000 : ℝ)|^4463 ≤ (27933859058677/100000000000000 : ℝ)^3439
        have hw : |(1871465439/5000000000 : ℝ)|=(1871465439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5173/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1223/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (159/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18661/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5173/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1223/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5173/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1223/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5173/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1223/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5173/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1223/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5173/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1223/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5173/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1223/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1223/50000 : ℝ) ^ (4461/1024 : ℝ) ≤ (4768355999353/50000000000000000000 : ℝ) := by
    have hpowers : (1223/50000 : ℝ)^4461 ≤ (4768355999353/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1223 : ℕ)^4461*50000000000000000000^1024 ≤ 4768355999353^1024*50000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1223 50000 4768355999353 50000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1223/50000 : ℝ)) (X := (4768355999353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5173/20000 : ℝ) ^ (4461/1024 : ℝ) ≤ (276384732143077333/100000000000000000000 : ℝ) := by
    have hpowers : (5173/20000 : ℝ)^4461 ≤ (276384732143077333/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5173 : ℕ)^4461*100000000000000000000^1024 ≤ 276384732143077333^1024*20000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5173 20000 276384732143077333 100000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5173/20000 : ℝ)) (X := (276384732143077333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000004768355999353/25000000000000000000 : ℝ) ≤ (400000017512831/400000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (25000004768355999353/25000000000000000000 : ℝ)^1024 ≤ (400000017512831/400000000000000 : ℝ)^4461 := by
      have hnat : (25000004768355999353 : ℕ)^1024*400000000000000^4461 ≤ 400000017512831^4461*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000004768355999353 25000000000000000000 400000017512831 400000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400000017512831/400000000000000 : ℝ)) (X := (25000004768355999353/25000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100276394268855076039/100000000000000000000 : ℝ) ≤ (2501584436612001/2500000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (100276394268855076039/100000000000000000000 : ℝ)^1024 ≤ (2501584436612001/2500000000000000 : ℝ)^4461 := by
      have hnat : (100276394268855076039 : ℕ)^1024*2500000000000000^4461 ≤ 2501584436612001^4461*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100276394268855076039 100000000000000000000 2501584436612001 2500000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501584436612001/2500000000000000 : ℝ)) (X := (100276394268855076039/100000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50276384732143077333/50000000000000000000 : ℝ) ≤ (10012675055075233/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (50276384732143077333/50000000000000000000 : ℝ)^1024 ≤ (10012675055075233/10000000000000000 : ℝ)^4461 := by
      have hnat : (50276384732143077333 : ℕ)^1024*10000000000000000^4461 ≤ 10012675055075233^4461*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50276384732143077333 50000000000000000000 10012675055075233 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012675055075233/10000000000000000 : ℝ)) (X := (50276384732143077333/50000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4768355999353/50000000000000000000 : ℝ) ≤ ((234159008139520325457/234190000000000000000 : ℝ)+2*(6337308627229/2341900000000000 : ℝ)*(1223/50000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (234159008139520325457/234190000000000000000 : ℝ)+2*(6337308627229/2341900000000000 : ℝ)*(1223/50000 : ℝ)=(400000017512831/400000000000000 : ℝ) by norm_num, show 1+2*(4768355999353/50000000000000000000 : ℝ)=(25000004768355999353/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(276384732143077333/100000000000000000000 : ℝ)+(4768355999353/50000000000000000000 : ℝ) ≤ ((234159008139520325457/234190000000000000000 : ℝ)+(6337308627229/2341900000000000 : ℝ)*((5173/20000 : ℝ)+(1223/50000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (234159008139520325457/234190000000000000000 : ℝ)+(6337308627229/2341900000000000 : ℝ)*((5173/20000 : ℝ)+(1223/50000 : ℝ))=(2501584436612001/2500000000000000 : ℝ) by norm_num, show 1+(276384732143077333/100000000000000000000 : ℝ)+(4768355999353/50000000000000000000 : ℝ)=(100276394268855076039/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(276384732143077333/100000000000000000000 : ℝ) ≤ ((234159008139520325457/234190000000000000000 : ℝ)+2*(6337308627229/2341900000000000 : ℝ)*(5173/20000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (234159008139520325457/234190000000000000000 : ℝ)+2*(6337308627229/2341900000000000 : ℝ)*(5173/20000 : ℝ)=(10012675055075233/10000000000000000 : ℝ) by norm_num, show 1+2*(276384732143077333/100000000000000000000 : ℝ)=(50276384732143077333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (234159008139520325457/234190000000000000000 : ℝ)*(X 1 0+X 2 0)+(6337308627229/2341900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (1223/50000 : ℝ)) (hi := (5173/20000 : ℝ)) (c := (234159008139520325457/234190000000000000000 : ℝ)) (alpha := (6337308627229/2341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (234159008139520325457/234190000000000000000 : ℝ)*(X 0 1+X 2 1)+(6337308627229/2341900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (1223/50000 : ℝ)) (hi := (5173/20000 : ℝ)) (c := (234159008139520325457/234190000000000000000 : ℝ)) (alpha := (6337308627229/2341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (234159008139520325457/234190000000000000000 : ℝ)*(X 0 2+X 1 2)+(6337308627229/2341900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (1223/50000 : ℝ)) (hi := (5173/20000 : ℝ)) (c := (234159008139520325457/234190000000000000000 : ℝ)) (alpha := (6337308627229/2341900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1878610117/10000000000 : ℝ)*X 0 0+(5590573681/10000000000 : ℝ)*X 0 1+(5083927679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5391997267/10000000000 : ℝ)*X 1 0+(-2146399483/10000000000 : ℝ)*X 1 1+(5083928387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((336999873/625000000 : ℝ)*X 2 0+(2541964049/5000000000 : ℝ)*X 2 1+(-429279787/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((852034979/2000000000 : ℝ)*X 0 0+(1864798913/5000000000 : ℝ)*X 0 1+(2427511331/5000000000 : ℝ)*X 0 2+(852034979/2000000000 : ℝ)*X 1 0+(1864798913/5000000000 : ℝ)*X 1 1+(2427511331/5000000000 : ℝ)*X 1 2+(852034979/2000000000 : ℝ)*X 2 0+(1864798913/5000000000 : ℝ)*X 2 1+(2427511331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375794487/2000000000 : ℝ)*X 0 0+(5089831031/10000000000 : ℝ)*X 0 1+(139614279/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((26295181/50000000 : ℝ)*X 1 0+(-164575617/1000000000 : ℝ)*X 1 1+(698071401/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5259036207/10000000000 : ℝ)*X 2 0+(5584571183/10000000000 : ℝ)*X 2 1+(-329151239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065245007/2500000000 : ℝ)*X 0 0+(968382053/2000000000 : ℝ)*X 0 1+(1871465439/5000000000 : ℝ)*X 0 2+(1065245007/2500000000 : ℝ)*X 1 0+(968382053/2000000000 : ℝ)*X 1 1+(1871465439/5000000000 : ℝ)*X 1 2+(1065245007/2500000000 : ℝ)*X 2 0+(968382053/2000000000 : ℝ)*X 2 1+(1871465439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4309616336882685539466615711/1463687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (540240639/100000000000000 : ℝ)*(base19) + (787444061/100000000000000 : ℝ)*(base23) + (17595479/100000000000000 : ℝ)*(upper4) + (183357771/100000000000000 : ℝ)*(upper5) + (357792337119541/25000000000000 : ℝ)*(major0) + (357792337119541/25000000000000 : ℝ)*(major1) + (357792337119541/25000000000000 : ℝ)*(major2) + (1973770260229179/100000000000000 : ℝ)*(sp0) + (61680556755083/3125000000000 : ℝ)*(sp1) + (986889255505577/50000000000000 : ℝ)*(sp2) + (177711319531161/20000000000000 : ℝ)*(sp3) + (9038226037/100000000000000 : ℝ)*(sp4) + (942051921/100000000000000 : ℝ)*(sp5) + (67567503/2500000000000 : ℝ)*(sp7) + (35542372014237/4000000000000 : ℝ)*(f.failure) + (123361206153451/6250000000000 : ℝ)*(f.sum) + (250274196777159/117095000000000000000000000000 : ℝ)*base66 + (57686731677112644763/5854750000000000000000000000000000 : ℝ)*base68 + (13258505530398894763/5854750000000000000000000000000000 : ℝ)*base70 + (28259683309414894763/5854750000000000000000000000000000 : ℝ)*base72 + (58636426349021/29273750000000000000000000000 : ℝ)*base74 + (6891862905449144763/5854750000000000000000000000000000 : ℝ)*base76 + (9238036593415105237/5854750000000000000000000000000000 : ℝ)*base77 + (3539738158181144763/5854750000000000000000000000000000 : ℝ)*base80 + (53186677743511/29273750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (528701/400000000000000000000 : ℝ)*base89 + (528701/400000000000000000000 : ℝ)*base91 + (528701/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25606038237129718527507474501/2927375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (834682263/50000000000000 : ℝ)*(base19) + (4458199/250000000000 : ℝ)*(base23) + (57449227/25000000000000 : ℝ)*(upper3) + (286967/625000000000 : ℝ)*(lower4) + (180018099/100000000000000 : ℝ)*(upper5) + (366399727007969/25000000000000 : ℝ)*(major0) + (366399727007969/25000000000000 : ℝ)*(major1) + (366399727007969/25000000000000 : ℝ)*(major2) + (10326746891/100000000000000 : ℝ)*(sp1) + (2818183871/25000000000000 : ℝ)*(sp2) + (505315550906571/25000000000000 : ℝ)*(sp4) + (505312551878717/25000000000000 : ℝ)*(sp5) + (2021249147611201/100000000000000 : ℝ)*(sp6) + (909935320867501/100000000000000 : ℝ)*(sp7) + (909935320867501/100000000000000 : ℝ)*(f.failure) + (505315550906571/25000000000000 : ℝ)*(f.sum) + (30976572637311/29273750000000000000000000000 : ℝ)*base65 + (4864781419149916833/5854750000000000000000000000000000 : ℝ)*base67 + (19810501805942166833/5854750000000000000000000000000000 : ℝ)*base69 + (9355246122258916833/5854750000000000000000000000000000 : ℝ)*base71 + (3968826175833/14636875000000000000000000000 : ℝ)*base73 + (30184648250032583167/5854750000000000000000000000000000 : ℝ)*base76 + (3358327441104416833/5854750000000000000000000000000000 : ℝ)*base77 + (17333101634402333167/5854750000000000000000000000000000 : ℝ)*base80 + (401379560937019/117095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (87106227/10000000000000000000000 : ℝ)*base90 + (87106227/10000000000000000000000 : ℝ)*base92 + (87106227/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5173/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1223/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (159/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18661/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1483_s2_0 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1906663211/10000000000 : ℝ)*x 0 + (1366954977/2500000000 : ℝ)*x 1 + (5188566627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1906663211/10000000000 : ℝ)^4463 ≤ (14550492021/125000000000 : ℝ)^3439 := by
    have hnat : (1906663211 : ℕ)^4463*125000000000^3439 ≤ 14550492021^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906663211 10000000000 14550492021 125000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366954977/2500000000 : ℝ)^4463 ≤ (45682041341387/100000000000000 : ℝ)^3439 := by
    have hnat : (1366954977 : ℕ)^4463*100000000000000^3439 ≤ 45682041341387^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366954977 2500000000 45682041341387 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188566627/10000000000 : ℝ)^4463 ≤ (21338782513159/50000000000000 : ℝ)^3439 := by
    have hnat : (5188566627 : ℕ)^4463*50000000000000^3439 ≤ 21338782513159^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188566627 10000000000 21338782513159 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1906663211/10000000000 : ℝ), (1366954977/2500000000 : ℝ), (5188566627/10000000000 : ℝ)] ![(14550492021/125000000000 : ℝ), (45682041341387/100000000000000 : ℝ), (21338782513159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1906663211/10000000000 : ℝ)|^4463 ≤ (14550492021/125000000000 : ℝ)^3439
        have hw : |(-1906663211/10000000000 : ℝ)|=(1906663211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366954977/2500000000 : ℝ)|^4463 ≤ (45682041341387/100000000000000 : ℝ)^3439
        have hw : |(1366954977/2500000000 : ℝ)|=(1366954977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188566627/10000000000 : ℝ)|^4463 ≤ (21338782513159/50000000000000 : ℝ)^3439
        have hw : |(5188566627/10000000000 : ℝ)|=(5188566627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_1 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361103069/10000000000 : ℝ)*x 0 + (-2050685061/10000000000 : ℝ)*x 1 + (207542651/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361103069/10000000000 : ℝ)^4463 ≤ (44528350751091/100000000000000 : ℝ)^3439 := by
    have hnat : (5361103069 : ℕ)^4463*100000000000000^3439 ≤ 44528350751091^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361103069 10000000000 44528350751091 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050685061/10000000000 : ℝ)^4463 ≤ (12794087953247/100000000000000 : ℝ)^3439 := by
    have hnat : (2050685061 : ℕ)^4463*100000000000000^3439 ≤ 12794087953247^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050685061 10000000000 12794087953247 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207542651/400000000 : ℝ)^4463 ≤ (42677561268899/100000000000000 : ℝ)^3439 := by
    have hnat : (207542651 : ℕ)^4463*100000000000000^3439 ≤ 42677561268899^3439*400000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207542651 400000000 42677561268899 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361103069/10000000000 : ℝ), (-2050685061/10000000000 : ℝ), (207542651/400000000 : ℝ)] ![(44528350751091/100000000000000 : ℝ), (12794087953247/100000000000000 : ℝ), (42677561268899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361103069/10000000000 : ℝ)|^4463 ≤ (44528350751091/100000000000000 : ℝ)^3439
        have hw : |(5361103069/10000000000 : ℝ)|=(5361103069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050685061/10000000000 : ℝ)|^4463 ≤ (12794087953247/100000000000000 : ℝ)^3439
        have hw : |(-2050685061/10000000000 : ℝ)|=(2050685061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207542651/400000000 : ℝ)|^4463 ≤ (42677561268899/100000000000000 : ℝ)^3439
        have hw : |(207542651/400000000 : ℝ)|=(207542651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_2 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361103059/10000000000 : ℝ)*x 0 + (5188566089/10000000000 : ℝ)*x 1 + (-2050685321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361103059/10000000000 : ℝ)^4463 ≤ (22264175321651/50000000000000 : ℝ)^3439 := by
    have hnat : (5361103059 : ℕ)^4463*50000000000000^3439 ≤ 22264175321651^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361103059 10000000000 22264175321651 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188566089/10000000000 : ℝ)^4463 ≤ (8535511856689/20000000000000 : ℝ)^3439 := by
    have hnat : (5188566089 : ℕ)^4463*20000000000000^3439 ≤ 8535511856689^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188566089 10000000000 8535511856689 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050685321/10000000000 : ℝ)^4463 ≤ (102352720467/800000000000 : ℝ)^3439 := by
    have hnat : (2050685321 : ℕ)^4463*800000000000^3439 ≤ 102352720467^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050685321 10000000000 102352720467 800000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361103059/10000000000 : ℝ), (5188566089/10000000000 : ℝ), (-2050685321/10000000000 : ℝ)] ![(22264175321651/50000000000000 : ℝ), (8535511856689/20000000000000 : ℝ), (102352720467/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361103059/10000000000 : ℝ)|^4463 ≤ (22264175321651/50000000000000 : ℝ)^3439
        have hw : |(5361103059/10000000000 : ℝ)|=(5361103059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188566089/10000000000 : ℝ)|^4463 ≤ (8535511856689/20000000000000 : ℝ)^3439
        have hw : |(5188566089/10000000000 : ℝ)|=(5188566089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050685321/10000000000 : ℝ)|^4463 ≤ (102352720467/800000000000 : ℝ)^3439
        have hw : |(-2050685321/10000000000 : ℝ)|=(2050685321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_3 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280207799/10000000000 : ℝ)*x 0 + (1989907307/5000000000 : ℝ)*x 1 + (2300063919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280207799/10000000000 : ℝ)^4463 ≤ (33245239721403/100000000000000 : ℝ)^3439 := by
    have hnat : (4280207799 : ℕ)^4463*100000000000000^3439 ≤ 33245239721403^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280207799 10000000000 33245239721403 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989907307/5000000000 : ℝ)^4463 ≤ (30249458970473/100000000000000 : ℝ)^3439 := by
    have hnat : (1989907307 : ℕ)^4463*100000000000000^3439 ≤ 30249458970473^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989907307 5000000000 30249458970473 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2300063919/5000000000 : ℝ)^4463 ≤ (4563162661151/12500000000000 : ℝ)^3439 := by
    have hnat : (2300063919 : ℕ)^4463*12500000000000^3439 ≤ 4563162661151^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300063919 5000000000 4563162661151 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280207799/10000000000 : ℝ), (1989907307/5000000000 : ℝ), (2300063919/5000000000 : ℝ)] ![(33245239721403/100000000000000 : ℝ), (30249458970473/100000000000000 : ℝ), (4563162661151/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280207799/10000000000 : ℝ)|^4463 ≤ (33245239721403/100000000000000 : ℝ)^3439
        have hw : |(4280207799/10000000000 : ℝ)|=(4280207799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1989907307/5000000000 : ℝ)|^4463 ≤ (30249458970473/100000000000000 : ℝ)^3439
        have hw : |(1989907307/5000000000 : ℝ)|=(1989907307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2300063919/5000000000 : ℝ)|^4463 ≤ (4563162661151/12500000000000 : ℝ)^3439
        have hw : |(2300063919/5000000000 : ℝ)|=(2300063919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_4 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-953361967/5000000000 : ℝ)*x 0 + (1297592261/2500000000 : ℝ)*x 1 + (5466000853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (953361967/5000000000 : ℝ)^4463 ≤ (1455109340751/12500000000000 : ℝ)^3439 := by
    have hnat : (953361967 : ℕ)^4463*12500000000000^3439 ≤ 1455109340751^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953361967 5000000000 1455109340751 12500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1297592261/2500000000 : ℝ)^4463 ≤ (42696805895169/100000000000000 : ℝ)^3439 := by
    have hnat : (1297592261 : ℕ)^4463*100000000000000^3439 ≤ 42696805895169^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297592261 2500000000 42696805895169 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466000853/10000000000 : ℝ)^4463 ≤ (9132463873957/20000000000000 : ℝ)^3439 := by
    have hnat : (5466000853 : ℕ)^4463*20000000000000^3439 ≤ 9132463873957^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466000853 10000000000 9132463873957 20000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-953361967/5000000000 : ℝ), (1297592261/2500000000 : ℝ), (5466000853/10000000000 : ℝ)] ![(1455109340751/12500000000000 : ℝ), (42696805895169/100000000000000 : ℝ), (9132463873957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-953361967/5000000000 : ℝ)|^4463 ≤ (1455109340751/12500000000000 : ℝ)^3439
        have hw : |(-953361967/5000000000 : ℝ)|=(953361967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1297592261/2500000000 : ℝ)|^4463 ≤ (42696805895169/100000000000000 : ℝ)^3439
        have hw : |(1297592261/2500000000 : ℝ)|=(1297592261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466000853/10000000000 : ℝ)|^4463 ≤ (9132463873957/20000000000000 : ℝ)^3439
        have hw : |(5466000853/10000000000 : ℝ)|=(5466000853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_5 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288105177/10000000000 : ℝ)*x 0 + (-1773251321/10000000000 : ℝ)*x 1 + (1366500213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288105177/10000000000 : ℝ)^4463 ≤ (43743109032317/100000000000000 : ℝ)^3439 := by
    have hnat : (5288105177 : ℕ)^4463*100000000000000^3439 ≤ 43743109032317^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288105177 10000000000 43743109032317 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1773251321/10000000000 : ℝ)^4463 ≤ (10594571597199/100000000000000 : ℝ)^3439 := by
    have hnat : (1773251321 : ℕ)^4463*100000000000000^3439 ≤ 10594571597199^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773251321 10000000000 10594571597199 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366500213/2500000000 : ℝ)^4463 ≤ (1426947479967/3125000000000 : ℝ)^3439 := by
    have hnat : (1366500213 : ℕ)^4463*3125000000000^3439 ≤ 1426947479967^3439*2500000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366500213 2500000000 1426947479967 3125000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288105177/10000000000 : ℝ), (-1773251321/10000000000 : ℝ), (1366500213/2500000000 : ℝ)] ![(43743109032317/100000000000000 : ℝ), (10594571597199/100000000000000 : ℝ), (1426947479967/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288105177/10000000000 : ℝ)|^4463 ≤ (43743109032317/100000000000000 : ℝ)^3439
        have hw : |(5288105177/10000000000 : ℝ)|=(5288105177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1773251321/10000000000 : ℝ)|^4463 ≤ (10594571597199/100000000000000 : ℝ)^3439
        have hw : |(-1773251321/10000000000 : ℝ)|=(1773251321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366500213/2500000000 : ℝ)|^4463 ≤ (1426947479967/3125000000000 : ℝ)^3439
        have hw : |(1366500213/2500000000 : ℝ)|=(1366500213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_6 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288105443/10000000000 : ℝ)*x 0 + (2733000447/5000000000 : ℝ)*x 1 + (-886625447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288105443/10000000000 : ℝ)^4463 ≤ (43743111887841/100000000000000 : ℝ)^3439 := by
    have hnat : (5288105443 : ℕ)^4463*100000000000000^3439 ≤ 43743111887841^3439*10000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288105443 10000000000 43743111887841 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733000447/5000000000 : ℝ)^4463 ≤ (1141557995357/2500000000000 : ℝ)^3439 := by
    have hnat : (2733000447 : ℕ)^4463*2500000000000^3439 ≤ 1141557995357^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733000447 5000000000 1141557995357 2500000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886625447/5000000000 : ℝ)^4463 ≤ (5297284143189/50000000000000 : ℝ)^3439 := by
    have hnat : (886625447 : ℕ)^4463*50000000000000^3439 ≤ 5297284143189^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886625447 5000000000 5297284143189 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288105443/10000000000 : ℝ), (2733000447/5000000000 : ℝ), (-886625447/5000000000 : ℝ)] ![(43743111887841/100000000000000 : ℝ), (1141557995357/2500000000000 : ℝ), (5297284143189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288105443/10000000000 : ℝ)|^4463 ≤ (43743111887841/100000000000000 : ℝ)^3439
        have hw : |(5288105443/10000000000 : ℝ)|=(5288105443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733000447/5000000000 : ℝ)|^4463 ≤ (1141557995357/2500000000000 : ℝ)^3439
        have hw : |(2733000447/5000000000 : ℝ)|=(2733000447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-886625447/5000000000 : ℝ)|^4463 ≤ (5297284143189/50000000000000 : ℝ)^3439
        have hw : |(-886625447/5000000000 : ℝ)|=(886625447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1483_s2_7 (p : ℝ) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267521431/625000000 : ℝ)*x 0 + (919224703/2000000000 : ℝ)*x 1 + (1991928107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267521431/625000000 : ℝ)^4463 ≤ (1662330075089/5000000000000 : ℝ)^3439 := by
    have hnat : (267521431 : ℕ)^4463*5000000000000^3439 ≤ 1662330075089^3439*625000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267521431 625000000 1662330075089 5000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (919224703/2000000000 : ℝ)^4463 ≤ (36464067471157/100000000000000 : ℝ)^3439 := by
    have hnat : (919224703 : ℕ)^4463*100000000000000^3439 ≤ 36464067471157^3439*2000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919224703 2000000000 36464067471157 100000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991928107/5000000000 : ℝ)^4463 ≤ (15144665504951/50000000000000 : ℝ)^3439 := by
    have hnat : (1991928107 : ℕ)^4463*50000000000000^3439 ≤ 15144665504951^3439*5000000000^4463 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991928107 5000000000 15144665504951 50000000000000 4463 3439 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4463/1024 : ℝ)) 4463 3439 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267521431/625000000 : ℝ), (919224703/2000000000 : ℝ), (1991928107/5000000000 : ℝ)] ![(1662330075089/5000000000000 : ℝ), (36464067471157/100000000000000 : ℝ), (15144665504951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267521431/625000000 : ℝ)|^4463 ≤ (1662330075089/5000000000000 : ℝ)^3439
        have hw : |(267521431/625000000 : ℝ)|=(267521431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(919224703/2000000000 : ℝ)|^4463 ≤ (36464067471157/100000000000000 : ℝ)^3439
        have hw : |(919224703/2000000000 : ℝ)|=(919224703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1991928107/5000000000 : ℝ)|^4463 ≤ (15144665504951/50000000000000 : ℝ)^3439
        have hw : |(1991928107/5000000000 : ℝ)|=(1991928107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1483_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (159/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (1021/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16117/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (159/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (159/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (159/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (159/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (159/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (159/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (159/2000 : ℝ) ^ (4461/1024 : ℝ) ≤ (809989774914511/50000000000000000000 : ℝ) := by
    have hpowers : (159/2000 : ℝ)^4461 ≤ (809989774914511/50000000000000000000 : ℝ)^1024 := by
      have hnat : (159 : ℕ)^4461*50000000000000000000^1024 ≤ 809989774914511^1024*2000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159 2000 809989774914511 50000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (159/2000 : ℝ)) (X := (809989774914511/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18661/100000 : ℝ) ^ (4461/1024 : ℝ) ≤ (33330192581929057/50000000000000000000 : ℝ) := by
    have hpowers : (18661/100000 : ℝ)^4461 ≤ (33330192581929057/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18661 : ℕ)^4461*50000000000000000000^1024 ≤ 33330192581929057^1024*100000^4461 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18661 100000 33330192581929057 50000000000000000000 4461 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18661/100000 : ℝ)) (X := (33330192581929057/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000809989774914511/25000000000000000000 : ℝ) ≤ (10000074370695129/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (25000809989774914511/25000000000000000000 : ℝ)^1024 ≤ (10000074370695129/10000000000000000 : ℝ)^4461 := by
      have hnat : (25000809989774914511 : ℕ)^1024*10000000000000000^4461 ≤ 10000074370695129^4461*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000809989774914511 25000000000000000000 10000074370695129 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000074370695129/10000000000000000 : ℝ)) (X := (25000809989774914511/25000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127133761397302723/3125000000000000000 : ℝ) ≤ (10001566929157637/10000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (3127133761397302723/3125000000000000000 : ℝ)^1024 ≤ (10001566929157637/10000000000000000 : ℝ)^4461 := by
      have hnat : (3127133761397302723 : ℕ)^1024*10000000000000000^4461 ≤ 10001566929157637^4461*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127133761397302723 3125000000000000000 10001566929157637 10000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001566929157637/10000000000000000 : ℝ)) (X := (3127133761397302723/3125000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25033330192581929057/25000000000000000000 : ℝ) ≤ (2000611897524029/2000000000000000 : ℝ) ^ (4461/1024 : ℝ) := by
    have hpowers : (25033330192581929057/25000000000000000000 : ℝ)^1024 ≤ (2000611897524029/2000000000000000 : ℝ)^4461 := by
      have hnat : (25033330192581929057 : ℕ)^1024*2000000000000000^4461 ≤ 2000611897524029^4461*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033330192581929057 25000000000000000000 2000611897524029 2000000000000000 1024 4461 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000611897524029/2000000000000000 : ℝ)) (X := (25033330192581929057/25000000000000000000 : ℝ)) (by norm_num) 4461 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(809989774914511/50000000000000000000 : ℝ) ≤ ((107087064904961649519/107110000000000000000 : ℝ)+2*(373139615627/267775000000000 : ℝ)*(159/2000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (107087064904961649519/107110000000000000000 : ℝ)+2*(373139615627/267775000000000 : ℝ)*(159/2000 : ℝ)=(10000074370695129/10000000000000000 : ℝ) by norm_num, show 1+2*(809989774914511/50000000000000000000 : ℝ)=(25000809989774914511/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33330192581929057/50000000000000000000 : ℝ)+(809989774914511/50000000000000000000 : ℝ) ≤ ((107087064904961649519/107110000000000000000 : ℝ)+(373139615627/267775000000000 : ℝ)*((18661/100000 : ℝ)+(159/2000 : ℝ)))^(4461/1024 : ℝ) := by
    rw [show (107087064904961649519/107110000000000000000 : ℝ)+(373139615627/267775000000000 : ℝ)*((18661/100000 : ℝ)+(159/2000 : ℝ))=(10001566929157637/10000000000000000 : ℝ) by norm_num, show 1+(33330192581929057/50000000000000000000 : ℝ)+(809989774914511/50000000000000000000 : ℝ)=(3127133761397302723/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33330192581929057/50000000000000000000 : ℝ) ≤ ((107087064904961649519/107110000000000000000 : ℝ)+2*(373139615627/267775000000000 : ℝ)*(18661/100000 : ℝ))^(4461/1024 : ℝ) := by
    rw [show (107087064904961649519/107110000000000000000 : ℝ)+2*(373139615627/267775000000000 : ℝ)*(18661/100000 : ℝ)=(2000611897524029/2000000000000000 : ℝ) by norm_num, show 1+2*(33330192581929057/50000000000000000000 : ℝ)=(25033330192581929057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (107087064904961649519/107110000000000000000 : ℝ)*(X 1 0+X 2 0)+(373139615627/267775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (159/2000 : ℝ)) (hi := (18661/100000 : ℝ)) (c := (107087064904961649519/107110000000000000000 : ℝ)) (alpha := (373139615627/267775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (107087064904961649519/107110000000000000000 : ℝ)*(X 0 1+X 2 1)+(373139615627/267775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (159/2000 : ℝ)) (hi := (18661/100000 : ℝ)) (c := (107087064904961649519/107110000000000000000 : ℝ)) (alpha := (373139615627/267775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (107087064904961649519/107110000000000000000 : ℝ)*(X 0 2+X 1 2)+(373139615627/267775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4461/1024 : ℝ)) (lo := (159/2000 : ℝ)) (hi := (18661/100000 : ℝ)) (c := (107087064904961649519/107110000000000000000 : ℝ)) (alpha := (373139615627/267775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1906663211/10000000000 : ℝ)*X 0 0+(1366954977/2500000000 : ℝ)*X 0 1+(5188566627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361103069/10000000000 : ℝ)*X 1 0+(-2050685061/10000000000 : ℝ)*X 1 1+(207542651/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361103059/10000000000 : ℝ)*X 2 0+(5188566089/10000000000 : ℝ)*X 2 1+(-2050685321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4280207799/10000000000 : ℝ)*X 0 0+(1989907307/5000000000 : ℝ)*X 0 1+(2300063919/5000000000 : ℝ)*X 0 2+(4280207799/10000000000 : ℝ)*X 1 0+(1989907307/5000000000 : ℝ)*X 1 1+(2300063919/5000000000 : ℝ)*X 1 2+(4280207799/10000000000 : ℝ)*X 2 0+(1989907307/5000000000 : ℝ)*X 2 1+(2300063919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-953361967/5000000000 : ℝ)*X 0 0+(1297592261/2500000000 : ℝ)*X 0 1+(5466000853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288105177/10000000000 : ℝ)*X 1 0+(-1773251321/10000000000 : ℝ)*X 1 1+(1366500213/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288105443/10000000000 : ℝ)*X 2 0+(2733000447/5000000000 : ℝ)*X 2 1+(-886625447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((267521431/625000000 : ℝ)*X 0 0+(919224703/2000000000 : ℝ)*X 0 1+(1991928107/5000000000 : ℝ)*X 0 2+(267521431/625000000 : ℝ)*X 1 0+(919224703/2000000000 : ℝ)*X 1 1+(1991928107/5000000000 : ℝ)*X 1 2+(267521431/625000000 : ℝ)*X 2 0+(919224703/2000000000 : ℝ)*X 2 1+(1991928107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1483_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17435813654224109967568859877/2677750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (887986033/50000000000000 : ℝ)*(base19) + (874801397/50000000000000 : ℝ)*(base23) + (140613111/50000000000000 : ℝ)*(upper3) + (422233/4000000000000 : ℝ)*(upper4) + (32523329/50000000000000 : ℝ)*(upper5) + (1298280817705239/50000000000000 : ℝ)*(major0) + (1298280817705239/50000000000000 : ℝ)*(major1) + (1298280817705239/50000000000000 : ℝ)*(major2) + (895249832347241/25000000000000 : ℝ)*(sp0) + (3581013673245721/100000000000000 : ℝ)*(sp1) + (1790506849807497/50000000000000 : ℝ)*(sp2) + (403024296385633/25000000000000 : ℝ)*(sp3) + (2014978603/12500000000000 : ℝ)*(sp4) + (2604753763/25000000000000 : ℝ)*(sp7) + (1612107604557583/100000000000000 : ℝ)*(f.failure) + (3581015449217787/100000000000000 : ℝ)*(f.sum) + (46067799989547/6694375000000000000000000000 : ℝ)*base66 + (6110142100131330041/5355500000000000000000000000000000 : ℝ)*base67 + (5024045371967330041/5355500000000000000000000000000000 : ℝ)*base69 + (26369709069190169959/5355500000000000000000000000000000 : ℝ)*base72 + (335640125560261/53555000000000000000000000000 : ℝ)*base74 + (22921226781854830041/5355500000000000000000000000000000 : ℝ)*base75 + (44639723637073669959/5355500000000000000000000000000000 : ℝ)*base78 + (2248189841892330041/5355500000000000000000000000000000 : ℝ)*base79 + (15948579670487/26777500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (92301841/10000000000000000000000 : ℝ)*base90 + (92301841/10000000000000000000000 : ℝ)*base92 + (92301841/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3580392847377888755378596011/669437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468826607/100000000000000 : ℝ)*(base19) + (374922377/50000000000000 : ℝ)*(base23) + (14140701/20000000000000 : ℝ)*(upper3) + (991537/6250000000000 : ℝ)*(lower4) + (157631739/100000000000000 : ℝ)*(upper5) + (657663085598123/25000000000000 : ℝ)*(major0) + (657663085598123/25000000000000 : ℝ)*(major1) + (657663085598123/25000000000000 : ℝ)*(major2) + (255014419/5000000000000 : ℝ)*(sp1) + (125802359/1250000000000 : ℝ)*(sp2) + (145121250490927/4000000000000 : ℝ)*(sp4) + (907006423289547/25000000000000 : ℝ)*(sp5) + (3628020448239701/100000000000000 : ℝ)*(sp6) + (1633273244233131/100000000000000 : ℝ)*(sp7) + (1633273244233131/100000000000000 : ℝ)*(f.failure) + (145121250490927/4000000000000 : ℝ)*(f.sum) + (37672010609003/26777500000000000000000000000 : ℝ)*base65 + (10165210815729902837/2677750000000000000000000000000000 : ℝ)*base67 + (13714626673366097163/2677750000000000000000000000000000 : ℝ)*base70 + (6027664810939347163/2677750000000000000000000000000000 : ℝ)*base72 + (336944075573901/53555000000000000000000000000 : ℝ)*base73 + (30188525987643847163/2677750000000000000000000000000000 : ℝ)*base76 + (10114740146863597163/2677750000000000000000000000000000 : ℝ)*base78 + (15779546620923597163/2677750000000000000000000000000000 : ℝ)*base80 + (5826327046959/13388750000000000000000000000 : ℝ)*base81 + (46709237/10000000000000000000000 : ℝ)*base90 + (46709237/10000000000000000000000 : ℝ)*base92 + (46709237/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1483_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (159/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1483_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1483_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1483_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1483_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1483_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4461/1024 : ℝ) ≤ p) (hpb : p ≤ (4463/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161066273/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1021/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16117/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1483_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
