-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1455_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:00:28.852128+00:00
-- url     : https://prove2.me/submissions/3f6d7cf6-bf98-4cfc-af50-8b35a45a0890

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
theorem support_rectangle_w1455_s6_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950228479/10000000000 : ℝ)*x 0 + (5406881473/10000000000 : ℝ)*x 1 + (2623727807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950228479/10000000000 : ℝ)^4415 ≤ (11904426562679/100000000000000 : ℝ)^3391 := by
    have hnat : (1950228479 : ℕ)^4415*100000000000000^3391 ≤ 11904426562679^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950228479 10000000000 11904426562679 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406881473/10000000000 : ℝ)^4415 ≤ (44905884558259/100000000000000 : ℝ)^3391 := by
    have hnat : (5406881473 : ℕ)^4415*100000000000000^3391 ≤ 44905884558259^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406881473 10000000000 44905884558259 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623727807/5000000000 : ℝ)^4415 ≤ (43189688874751/100000000000000 : ℝ)^3391 := by
    have hnat : (2623727807 : ℕ)^4415*100000000000000^3391 ≤ 43189688874751^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623727807 5000000000 43189688874751 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950228479/10000000000 : ℝ), (5406881473/10000000000 : ℝ), (2623727807/5000000000 : ℝ)] ![(11904426562679/100000000000000 : ℝ), (44905884558259/100000000000000 : ℝ), (43189688874751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950228479/10000000000 : ℝ)|^4415 ≤ (11904426562679/100000000000000 : ℝ)^3391
        have hw : |(-1950228479/10000000000 : ℝ)|=(1950228479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406881473/10000000000 : ℝ)|^4415 ≤ (44905884558259/100000000000000 : ℝ)^3391
        have hw : |(5406881473/10000000000 : ℝ)|=(5406881473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623727807/5000000000 : ℝ)|^4415 ≤ (43189688874751/100000000000000 : ℝ)^3391
        have hw : |(2623727807/5000000000 : ℝ)|=(2623727807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336691899/2500000000 : ℝ)*x 0 + (-507844339/2500000000 : ℝ)*x 1 + (5247455603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336691899/2500000000 : ℝ)^4415 ≤ (44256947602671/100000000000000 : ℝ)^3391 := by
    have hnat : (1336691899 : ℕ)^4415*100000000000000^3391 ≤ 44256947602671^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336691899 2500000000 44256947602671 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507844339/2500000000 : ℝ)^4415 ≤ (12553363629943/100000000000000 : ℝ)^3391 := by
    have hnat : (507844339 : ℕ)^4415*100000000000000^3391 ≤ 12553363629943^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507844339 2500000000 12553363629943 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247455603/10000000000 : ℝ)^4415 ≤ (69103502011/160000000000 : ℝ)^3391 := by
    have hnat : (5247455603 : ℕ)^4415*160000000000^3391 ≤ 69103502011^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247455603 10000000000 69103502011 160000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336691899/2500000000 : ℝ), (-507844339/2500000000 : ℝ), (5247455603/10000000000 : ℝ)] ![(44256947602671/100000000000000 : ℝ), (12553363629943/100000000000000 : ℝ), (69103502011/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336691899/2500000000 : ℝ)|^4415 ≤ (44256947602671/100000000000000 : ℝ)^3391
        have hw : |(1336691899/2500000000 : ℝ)|=(1336691899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507844339/2500000000 : ℝ)|^4415 ≤ (12553363629943/100000000000000 : ℝ)^3391
        have hw : |(-507844339/2500000000 : ℝ)|=(507844339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247455603/10000000000 : ℝ)|^4415 ≤ (69103502011/160000000000 : ℝ)^3391
        have hw : |(5247455603/10000000000 : ℝ)|=(5247455603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346767603/10000000000 : ℝ)*x 0 + (5247455609/10000000000 : ℝ)*x 1 + (-1015688669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346767603/10000000000 : ℝ)^4415 ≤ (4425694767811/10000000000000 : ℝ)^3391 := by
    have hnat : (5346767603 : ℕ)^4415*10000000000000^3391 ≤ 4425694767811^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346767603 10000000000 4425694767811 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247455609/10000000000 : ℝ)^4415 ≤ (43189688821171/100000000000000 : ℝ)^3391 := by
    have hnat : (5247455609 : ℕ)^4415*100000000000000^3391 ≤ 43189688821171^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247455609 10000000000 43189688821171 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015688669/5000000000 : ℝ)^4415 ≤ (6276681742559/50000000000000 : ℝ)^3391 := by
    have hnat : (1015688669 : ℕ)^4415*50000000000000^3391 ≤ 6276681742559^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015688669 5000000000 6276681742559 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346767603/10000000000 : ℝ), (5247455609/10000000000 : ℝ), (-1015688669/5000000000 : ℝ)] ![(4425694767811/10000000000000 : ℝ), (43189688821171/100000000000000 : ℝ), (6276681742559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346767603/10000000000 : ℝ)|^4415 ≤ (4425694767811/10000000000000 : ℝ)^3391
        have hw : |(5346767603/10000000000 : ℝ)|=(5346767603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247455609/10000000000 : ℝ)|^4415 ≤ (43189688821171/100000000000000 : ℝ)^3391
        have hw : |(5247455609/10000000000 : ℝ)|=(5247455609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1015688669/5000000000 : ℝ)|^4415 ≤ (6276681742559/50000000000000 : ℝ)^3391
        have hw : |(-1015688669/5000000000 : ℝ)|=(1015688669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297914339/10000000000 : ℝ)*x 0 + (4126960539/10000000000 : ℝ)*x 1 + (4475140197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297914339/10000000000 : ℝ)^4415 ≤ (3330507883211/10000000000000 : ℝ)^3391 := by
    have hnat : (4297914339 : ℕ)^4415*10000000000000^3391 ≤ 3330507883211^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297914339 10000000000 3330507883211 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126960539/10000000000 : ℝ)^4415 ≤ (15795376084649/50000000000000 : ℝ)^3391 := by
    have hnat : (4126960539 : ℕ)^4415*50000000000000^3391 ≤ 15795376084649^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126960539 10000000000 15795376084649 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475140197/10000000000 : ℝ)^4415 ≤ (35104168977141/100000000000000 : ℝ)^3391 := by
    have hnat : (4475140197 : ℕ)^4415*100000000000000^3391 ≤ 35104168977141^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475140197 10000000000 35104168977141 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297914339/10000000000 : ℝ), (4126960539/10000000000 : ℝ), (4475140197/10000000000 : ℝ)] ![(3330507883211/10000000000000 : ℝ), (15795376084649/50000000000000 : ℝ), (35104168977141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297914339/10000000000 : ℝ)|^4415 ≤ (3330507883211/10000000000000 : ℝ)^3391
        have hw : |(4297914339/10000000000 : ℝ)|=(4297914339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126960539/10000000000 : ℝ)|^4415 ≤ (15795376084649/50000000000000 : ℝ)^3391
        have hw : |(4126960539/10000000000 : ℝ)|=(4126960539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475140197/10000000000 : ℝ)|^4415 ≤ (35104168977141/100000000000000 : ℝ)^3391
        have hw : |(4475140197/10000000000 : ℝ)|=(4475140197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-78009581/400000000 : ℝ)*x 0 + (524803229/1000000000 : ℝ)*x 1 + (5406301847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (78009581/400000000 : ℝ)^4415 ≤ (5952257174951/50000000000000 : ℝ)^3391 := by
    have hnat : (78009581 : ℕ)^4415*50000000000000^3391 ≤ 5952257174951^3391*400000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78009581 400000000 5952257174951 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524803229/1000000000 : ℝ)^4415 ≤ (43195868658861/100000000000000 : ℝ)^3391 := by
    have hnat : (524803229 : ℕ)^4415*100000000000000^3391 ≤ 43195868658861^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524803229 1000000000 43195868658861 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406301847/10000000000 : ℝ)^4415 ≤ (44899616974409/100000000000000 : ℝ)^3391 := by
    have hnat : (5406301847 : ℕ)^4415*100000000000000^3391 ≤ 44899616974409^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406301847 10000000000 44899616974409 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-78009581/400000000 : ℝ), (524803229/1000000000 : ℝ), (5406301847/10000000000 : ℝ)] ![(5952257174951/50000000000000 : ℝ), (43195868658861/100000000000000 : ℝ), (44899616974409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-78009581/400000000 : ℝ)|^4415 ≤ (5952257174951/50000000000000 : ℝ)^3391
        have hw : |(-78009581/400000000 : ℝ)|=(78009581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524803229/1000000000 : ℝ)|^4415 ≤ (43195868658861/100000000000000 : ℝ)^3391
        have hw : |(524803229/1000000000 : ℝ)|=(524803229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406301847/10000000000 : ℝ)|^4415 ≤ (44899616974409/100000000000000 : ℝ)^3391
        have hw : |(5406301847/10000000000 : ℝ)|=(5406301847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652608973/5000000000 : ℝ)*x 0 + (-374506217/2000000000 : ℝ)*x 1 + (135157551/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652608973/5000000000 : ℝ)^4415 ≤ (43809698328119/100000000000000 : ℝ)^3391 := by
    have hnat : (2652608973 : ℕ)^4415*100000000000000^3391 ≤ 43809698328119^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652608973 5000000000 43809698328119 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374506217/2000000000 : ℝ)^4415 ≤ (1129068259601/10000000000000 : ℝ)^3391 := by
    have hnat : (374506217 : ℕ)^4415*10000000000000^3391 ≤ 1129068259601^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374506217 2000000000 1129068259601 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135157551/250000000 : ℝ)^4415 ≤ (22449809530657/50000000000000 : ℝ)^3391 := by
    have hnat : (135157551 : ℕ)^4415*50000000000000^3391 ≤ 22449809530657^3391*250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135157551 250000000 22449809530657 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652608973/5000000000 : ℝ), (-374506217/2000000000 : ℝ), (135157551/250000000 : ℝ)] ![(43809698328119/100000000000000 : ℝ), (1129068259601/10000000000000 : ℝ), (22449809530657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652608973/5000000000 : ℝ)|^4415 ≤ (43809698328119/100000000000000 : ℝ)^3391
        have hw : |(2652608973/5000000000 : ℝ)|=(2652608973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374506217/2000000000 : ℝ)|^4415 ≤ (1129068259601/10000000000000 : ℝ)^3391
        have hw : |(-374506217/2000000000 : ℝ)|=(374506217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135157551/250000000 : ℝ)|^4415 ≤ (22449809530657/50000000000000 : ℝ)^3391
        have hw : |(135157551/250000000 : ℝ)|=(135157551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_6 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530521737/1000000000 : ℝ)*x 0 + (5406302767/10000000000 : ℝ)*x 1 + (-1872530873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530521737/1000000000 : ℝ)^4415 ≤ (21904846067621/50000000000000 : ℝ)^3391 := by
    have hnat : (530521737 : ℕ)^4415*50000000000000^3391 ≤ 21904846067621^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530521737 1000000000 21904846067621 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406302767/10000000000 : ℝ)^4415 ≤ (11224906730587/25000000000000 : ℝ)^3391 := by
    have hnat : (5406302767 : ℕ)^4415*25000000000000^3391 ≤ 11224906730587^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406302767 10000000000 11224906730587 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872530873/10000000000 : ℝ)^4415 ≤ (2822670232929/25000000000000 : ℝ)^3391 := by
    have hnat : (1872530873 : ℕ)^4415*25000000000000^3391 ≤ 2822670232929^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872530873 10000000000 2822670232929 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530521737/1000000000 : ℝ), (5406302767/10000000000 : ℝ), (-1872530873/10000000000 : ℝ)] ![(21904846067621/50000000000000 : ℝ), (11224906730587/25000000000000 : ℝ), (2822670232929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530521737/1000000000 : ℝ)|^4415 ≤ (21904846067621/50000000000000 : ℝ)^3391
        have hw : |(530521737/1000000000 : ℝ)|=(530521737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406302767/10000000000 : ℝ)|^4415 ≤ (11224906730587/25000000000000 : ℝ)^3391
        have hw : |(5406302767/10000000000 : ℝ)|=(5406302767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1872530873/10000000000 : ℝ)|^4415 ≤ (2822670232929/25000000000000 : ℝ)^3391
        have hw : |(-1872530873/10000000000 : ℝ)|=(1872530873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s6_7 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074484579/2500000000 : ℝ)*x 0 + (2236940843/5000000000 : ℝ)*x 1 + (2064112913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074484579/2500000000 : ℝ)^4415 ≤ (1040791273139/3125000000000 : ℝ)^3391 := by
    have hnat : (1074484579 : ℕ)^4415*3125000000000^3391 ≤ 1040791273139^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074484579 2500000000 1040791273139 3125000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236940843/5000000000 : ℝ)^4415 ≤ (35091316301643/100000000000000 : ℝ)^3391 := by
    have hnat : (2236940843 : ℕ)^4415*100000000000000^3391 ≤ 35091316301643^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236940843 5000000000 35091316301643 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064112913/5000000000 : ℝ)^4415 ≤ (31603362942539/100000000000000 : ℝ)^3391 := by
    have hnat : (2064112913 : ℕ)^4415*100000000000000^3391 ≤ 31603362942539^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064112913 5000000000 31603362942539 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074484579/2500000000 : ℝ), (2236940843/5000000000 : ℝ), (2064112913/5000000000 : ℝ)] ![(1040791273139/3125000000000 : ℝ), (35091316301643/100000000000000 : ℝ), (31603362942539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074484579/2500000000 : ℝ)|^4415 ≤ (1040791273139/3125000000000 : ℝ)^3391
        have hw : |(1074484579/2500000000 : ℝ)|=(1074484579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236940843/5000000000 : ℝ)|^4415 ≤ (35091316301643/100000000000000 : ℝ)^3391
        have hw : |(2236940843/5000000000 : ℝ)|=(2236940843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064112913/5000000000 : ℝ)|^4415 ≤ (31603362942539/100000000000000 : ℝ)^3391
        have hw : |(2064112913/5000000000 : ℝ)|=(2064112913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (356/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11389/100000 : ℝ) ^ (2207/512 : ℝ) ≤ (8569133743606119/100000000000000000000 : ℝ) := by
    have hpowers : (11389/100000 : ℝ)^2207 ≤ (8569133743606119/100000000000000000000 : ℝ)^512 := by
      have hnat : (11389 : ℕ)^2207*100000000000000000000^512 ≤ 8569133743606119^512*100000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11389 100000 8569133743606119 100000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11389/100000 : ℝ)) (X := (8569133743606119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (2207/512 : ℝ) ≤ (2630000861973333/10000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^2207 ≤ (2630000861973333/10000000000000000000 : ℝ)^512 := by
      have hnat : (14773 : ℕ)^2207*10000000000000000000^512 ≤ 2630000861973333^512*100000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 2630000861973333 10000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (2630000861973333/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008569133743606119/50000000000000000000 : ℝ) ≤ (625024847687829/625000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (50008569133743606119/50000000000000000000 : ℝ)^512 ≤ (625024847687829/625000000000000 : ℝ)^2207 := by
      have hnat : (50008569133743606119 : ℕ)^512*625000000000000^2207 ≤ 625024847687829^2207*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008569133743606119 50000000000000000000 625024847687829 625000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625024847687829/625000000000000 : ℝ)) (X := (50008569133743606119/50000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034869142363339449/100000000000000000000 : ℝ) ≤ (2000161763578387/2000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (100034869142363339449/100000000000000000000 : ℝ)^512 ≤ (2000161763578387/2000000000000000 : ℝ)^2207 := by
      have hnat : (100034869142363339449 : ℕ)^512*2000000000000000^2207 ≤ 2000161763578387^2207*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034869142363339449 100000000000000000000 2000161763578387 2000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000161763578387/2000000000000000 : ℝ)) (X := (100034869142363339449/100000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002630000861973333/5000000000000000000 : ℝ) ≤ (5000610036389303/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (5002630000861973333/5000000000000000000 : ℝ)^512 ≤ (5000610036389303/5000000000000000 : ℝ)^2207 := by
      have hnat : (5002630000861973333 : ℕ)^512*5000000000000000^2207 ≤ 5000610036389303^2207*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002630000861973333 5000000000000000000 5000610036389303 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000610036389303/5000000000000000 : ℝ)) (X := (5002630000861973333/5000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8569133743606119/100000000000000000000 : ℝ) ≤ ((16915988894700610669/16920000000000000000 : ℝ)+2*(411254886671/338400000000000 : ℝ)*(11389/100000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (16915988894700610669/16920000000000000000 : ℝ)+2*(411254886671/338400000000000 : ℝ)*(11389/100000 : ℝ)=(625024847687829/625000000000000 : ℝ) by norm_num, show 1+2*(8569133743606119/100000000000000000000 : ℝ)=(50008569133743606119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2630000861973333/10000000000000000000 : ℝ)+(8569133743606119/100000000000000000000 : ℝ) ≤ ((16915988894700610669/16920000000000000000 : ℝ)+(411254886671/338400000000000 : ℝ)*((14773/100000 : ℝ)+(11389/100000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (16915988894700610669/16920000000000000000 : ℝ)+(411254886671/338400000000000 : ℝ)*((14773/100000 : ℝ)+(11389/100000 : ℝ))=(2000161763578387/2000000000000000 : ℝ) by norm_num, show 1+(2630000861973333/10000000000000000000 : ℝ)+(8569133743606119/100000000000000000000 : ℝ)=(100034869142363339449/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2630000861973333/10000000000000000000 : ℝ) ≤ ((16915988894700610669/16920000000000000000 : ℝ)+2*(411254886671/338400000000000 : ℝ)*(14773/100000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (16915988894700610669/16920000000000000000 : ℝ)+2*(411254886671/338400000000000 : ℝ)*(14773/100000 : ℝ)=(5000610036389303/5000000000000000 : ℝ) by norm_num, show 1+2*(2630000861973333/10000000000000000000 : ℝ)=(5002630000861973333/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16915988894700610669/16920000000000000000 : ℝ)*(X 1 0+X 2 0)+(411254886671/338400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (16915988894700610669/16920000000000000000 : ℝ)) (alpha := (411254886671/338400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16915988894700610669/16920000000000000000 : ℝ)*(X 0 1+X 2 1)+(411254886671/338400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (16915988894700610669/16920000000000000000 : ℝ)) (alpha := (411254886671/338400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16915988894700610669/16920000000000000000 : ℝ)*(X 0 2+X 1 2)+(411254886671/338400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11389/100000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (16915988894700610669/16920000000000000000 : ℝ)) (alpha := (411254886671/338400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1950228479/10000000000 : ℝ)*X 0 0+(5406881473/10000000000 : ℝ)*X 0 1+(2623727807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336691899/2500000000 : ℝ)*X 1 0+(-507844339/2500000000 : ℝ)*X 1 1+(5247455603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346767603/10000000000 : ℝ)*X 2 0+(5247455609/10000000000 : ℝ)*X 2 1+(-1015688669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297914339/10000000000 : ℝ)*X 0 0+(4126960539/10000000000 : ℝ)*X 0 1+(4475140197/10000000000 : ℝ)*X 0 2+(4297914339/10000000000 : ℝ)*X 1 0+(4126960539/10000000000 : ℝ)*X 1 1+(4475140197/10000000000 : ℝ)*X 1 2+(4297914339/10000000000 : ℝ)*X 2 0+(4126960539/10000000000 : ℝ)*X 2 1+(4475140197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-78009581/400000000 : ℝ)*X 0 0+(524803229/1000000000 : ℝ)*X 0 1+(5406301847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652608973/5000000000 : ℝ)*X 1 0+(-374506217/2000000000 : ℝ)*X 1 1+(135157551/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530521737/1000000000 : ℝ)*X 2 0+(5406302767/10000000000 : ℝ)*X 2 1+(-1872530873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074484579/2500000000 : ℝ)*X 0 0+(2236940843/5000000000 : ℝ)*X 0 1+(2064112913/5000000000 : ℝ)*X 0 2+(1074484579/2500000000 : ℝ)*X 1 0+(2236940843/5000000000 : ℝ)*X 1 1+(2064112913/5000000000 : ℝ)*X 1 2+(1074484579/2500000000 : ℝ)*X 2 0+(2236940843/5000000000 : ℝ)*X 2 1+(2064112913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1153502756409376953706119677/141000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1493292531/100000000000000 : ℝ)*(base19) + (703280409/50000000000000 : ℝ)*(base23) + (5076423/10000000000000 : ℝ)*(lower2) + (38402857/20000000000000 : ℝ)*(upper3) + (36856163/25000000000000 : ℝ)*(upper5) + (2286170868166811/50000000000000 : ℝ)*(major0) + (2286170868166811/50000000000000 : ℝ)*(major1) + (2286170868166811/50000000000000 : ℝ)*(major2) + (3136270260240469/50000000000000 : ℝ)*(sp0) + (1254514236560183/20000000000000 : ℝ)*(sp1) + (6272571269532627/100000000000000 : ℝ)*(sp2) + (718023724222331/25000000000000 : ℝ)*(sp3) + (8038903127/25000000000000 : ℝ)*(sp4) + (781349439/5000000000000 : ℝ)*(sp7) + (359013815484763/12500000000000 : ℝ)*(f.failure) + (3136286338046723/50000000000000 : ℝ)*(f.sum) + (40553764279741/8460000000000000000000000000 : ℝ)*base65 + (11416966080592643441/846000000000000000000000000000000 : ℝ)*base68 + (14367698691268643441/846000000000000000000000000000000 : ℝ)*base70 + (1521090842908643441/846000000000000000000000000000000 : ℝ)*base72 + (19946137800779/8460000000000000000000000000 : ℝ)*base74 + (1800781993570643441/846000000000000000000000000000000 : ℝ)*base76 + (6727317941794643441/846000000000000000000000000000000 : ℝ)*base78 + (356285812846643441/846000000000000000000000000000000 : ℝ)*base80 + (29933964783539/8460000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6985399/1250000000000000000000 : ℝ)*base89 + (6985399/1250000000000000000000 : ℝ)*base91 + (6985399/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1410027640023215972703411283/141000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812079857/100000000000000 : ℝ)*(base19) + (72700011/25000000000000 : ℝ)*(base23) + (94367961/50000000000000 : ℝ)*(lower1) + (153126167/50000000000000 : ℝ)*(upper3) + (5008971/25000000000000 : ℝ)*(lower4) + (4605678418173593/100000000000000 : ℝ)*(major0) + (4605678418173593/100000000000000 : ℝ)*(major1) + (4605678418173593/100000000000000 : ℝ)*(major2) + (16208861243/100000000000000 : ℝ)*(sp2) + (1497509987/100000000000000 : ℝ)*(sp3) + (6318305585723581/100000000000000 : ℝ)*(sp4) + (1579576193410931/25000000000000 : ℝ)*(sp5) + (3159144543031147/50000000000000 : ℝ)*(sp6) + (578609883954747/20000000000000 : ℝ)*(sp7) + (1446525458641861/50000000000000 : ℝ)*(f.failure) + (6318305585723581/100000000000000 : ℝ)*(f.sum) + (34031156610857/16920000000000000000000000000 : ℝ)*base66 + (8908092026139013717/1692000000000000000000000000000000 : ℝ)*base67 + (5958037636743013717/1692000000000000000000000000000000 : ℝ)*base69 + (12124830949851013717/1692000000000000000000000000000000 : ℝ)*base71 + (63371110380943/16920000000000000000000000000 : ℝ)*base73 + (5107565929467013717/1692000000000000000000000000000000 : ℝ)*base75 + (62461007952591013717/1692000000000000000000000000000000 : ℝ)*base77 + (75974808673400986283/1692000000000000000000000000000000 : ℝ)*base80 + (24105643178143/16920000000000000000000000000 : ℝ)*base81 + (45852247/5000000000000000000000 : ℝ)*base90 + (45852247/5000000000000000000000 : ℝ)*base92 + (45852247/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1455_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1455_s7_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950230441/10000000000 : ℝ)*x 0 + (337928799/625000000 : ℝ)*x 1 + (1049495007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950230441/10000000000 : ℝ)^4415 ≤ (1190444215551/10000000000000 : ℝ)^3391 := by
    have hnat : (1950230441 : ℕ)^4415*10000000000000^3391 ≤ 1190444215551^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950230441 10000000000 1190444215551 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337928799/625000000 : ℝ)^4415 ≤ (87706368831/195312500000 : ℝ)^3391 := by
    have hnat : (337928799 : ℕ)^4415*195312500000^3391 ≤ 87706368831^3391*625000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337928799 625000000 87706368831 195312500000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049495007/2000000000 : ℝ)^4415 ≤ (4318989699103/10000000000000 : ℝ)^3391 := by
    have hnat : (1049495007 : ℕ)^4415*10000000000000^3391 ≤ 4318989699103^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049495007 2000000000 4318989699103 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950230441/10000000000 : ℝ), (337928799/625000000 : ℝ), (1049495007/2000000000 : ℝ)] ![(1190444215551/10000000000000 : ℝ), (87706368831/195312500000 : ℝ), (4318989699103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950230441/10000000000 : ℝ)|^4415 ≤ (1190444215551/10000000000000 : ℝ)^3391
        have hw : |(-1950230441/10000000000 : ℝ)|=(1950230441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337928799/625000000 : ℝ)|^4415 ≤ (87706368831/195312500000 : ℝ)^3391
        have hw : |(337928799/625000000 : ℝ)|=(337928799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049495007/2000000000 : ℝ)|^4415 ≤ (4318989699103/10000000000000 : ℝ)^3391
        have hw : |(1049495007/2000000000 : ℝ)|=(1049495007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s7_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346762327/10000000000 : ℝ)*x 0 + (-50783963/250000000 : ℝ)*x 1 + (1311868761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346762327/10000000000 : ℝ)^4415 ≤ (1383027838103/3125000000000 : ℝ)^3391 := by
    have hnat : (5346762327 : ℕ)^4415*3125000000000^3391 ≤ 1383027838103^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346762327 10000000000 1383027838103 3125000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50783963/250000000 : ℝ)^4415 ≤ (6276606039177/50000000000000 : ℝ)^3391 := by
    have hnat : (50783963 : ℕ)^4415*50000000000000^3391 ≤ 6276606039177^3391*250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50783963 250000000 6276606039177 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311868761/2500000000 : ℝ)^4415 ≤ (21594948543737/50000000000000 : ℝ)^3391 := by
    have hnat : (1311868761 : ℕ)^4415*50000000000000^3391 ≤ 21594948543737^3391*2500000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311868761 2500000000 21594948543737 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346762327/10000000000 : ℝ), (-50783963/250000000 : ℝ), (1311868761/2500000000 : ℝ)] ![(1383027838103/3125000000000 : ℝ), (6276606039177/50000000000000 : ℝ), (21594948543737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346762327/10000000000 : ℝ)|^4415 ≤ (1383027838103/3125000000000 : ℝ)^3391
        have hw : |(5346762327/10000000000 : ℝ)|=(5346762327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50783963/250000000 : ℝ)|^4415 ≤ (6276606039177/50000000000000 : ℝ)^3391
        have hw : |(-50783963/250000000 : ℝ)|=(50783963/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311868761/2500000000 : ℝ)|^4415 ≤ (21594948543737/50000000000000 : ℝ)^3391
        have hw : |(1311868761/2500000000 : ℝ)|=(1311868761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s7_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673381161/5000000000 : ℝ)*x 0 + (5247475051/10000000000 : ℝ)*x 1 + (-2031358517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673381161/5000000000 : ℝ)^4415 ≤ (11064222691353/25000000000000 : ℝ)^3391 := by
    have hnat : (2673381161 : ℕ)^4415*25000000000000^3391 ≤ 11064222691353^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673381161 5000000000 11064222691353 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247475051/10000000000 : ℝ)^4415 ≤ (21594948581243/50000000000000 : ℝ)^3391 := by
    have hnat : (5247475051 : ℕ)^4415*50000000000000^3391 ≤ 21594948581243^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247475051 10000000000 21594948581243 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2031358517/10000000000 : ℝ)^4415 ≤ (12553212054217/100000000000000 : ℝ)^3391 := by
    have hnat : (2031358517 : ℕ)^4415*100000000000000^3391 ≤ 12553212054217^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031358517 10000000000 12553212054217 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673381161/5000000000 : ℝ), (5247475051/10000000000 : ℝ), (-2031358517/10000000000 : ℝ)] ![(11064222691353/25000000000000 : ℝ), (21594948581243/50000000000000 : ℝ), (12553212054217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673381161/5000000000 : ℝ)|^4415 ≤ (11064222691353/25000000000000 : ℝ)^3391
        have hw : |(2673381161/5000000000 : ℝ)|=(2673381161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247475051/10000000000 : ℝ)|^4415 ≤ (21594948581243/50000000000000 : ℝ)^3391
        have hw : |(5247475051/10000000000 : ℝ)|=(5247475051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2031358517/10000000000 : ℝ)|^4415 ≤ (12553212054217/100000000000000 : ℝ)^3391
        have hw : |(-2031358517/10000000000 : ℝ)|=(2031358517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s7_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148957869/5000000000 : ℝ)*x 0 + (4127004223/10000000000 : ℝ)*x 1 + (2237548093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148957869/5000000000 : ℝ)^4415 ≤ (6661018589373/20000000000000 : ℝ)^3391 := by
    have hnat : (2148957869 : ℕ)^4415*20000000000000^3391 ≤ 6661018589373^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148957869 5000000000 6661018589373 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127004223/10000000000 : ℝ)^4415 ≤ (7897796884113/25000000000000 : ℝ)^3391 := by
    have hnat : (4127004223 : ℕ)^4415*25000000000000^3391 ≤ 7897796884113^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127004223 10000000000 7897796884113 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237548093/5000000000 : ℝ)^4415 ≤ (35103719491771/100000000000000 : ℝ)^3391 := by
    have hnat : (2237548093 : ℕ)^4415*100000000000000^3391 ≤ 35103719491771^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237548093 5000000000 35103719491771 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148957869/5000000000 : ℝ), (4127004223/10000000000 : ℝ), (2237548093/5000000000 : ℝ)] ![(6661018589373/20000000000000 : ℝ), (7897796884113/25000000000000 : ℝ), (35103719491771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148957869/5000000000 : ℝ)|^4415 ≤ (6661018589373/20000000000000 : ℝ)^3391
        have hw : |(2148957869/5000000000 : ℝ)|=(2148957869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127004223/10000000000 : ℝ)|^4415 ≤ (7897796884113/25000000000000 : ℝ)^3391
        have hw : |(4127004223/10000000000 : ℝ)|=(4127004223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237548093/5000000000 : ℝ)|^4415 ≤ (35103719491771/100000000000000 : ℝ)^3391
        have hw : |(2237548093/5000000000 : ℝ)|=(2237548093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s7_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1950242251/10000000000 : ℝ)*x 0 + (5248050787/10000000000 : ℝ)*x 1 + (675785189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1950242251/10000000000 : ℝ)^4415 ≤ (5952268007299/50000000000000 : ℝ)^3391 := by
    have hnat : (1950242251 : ℕ)^4415*50000000000000^3391 ≤ 5952268007299^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950242251 10000000000 5952268007299 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5248050787/10000000000 : ℝ)^4415 ≤ (5399508360011/12500000000000 : ℝ)^3391 := by
    have hnat : (5248050787 : ℕ)^4415*12500000000000^3391 ≤ 5399508360011^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248050787 10000000000 5399508360011 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675785189/1250000000 : ℝ)^4415 ≤ (22449698546327/50000000000000 : ℝ)^3391 := by
    have hnat : (675785189 : ℕ)^4415*50000000000000^3391 ≤ 22449698546327^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675785189 1250000000 22449698546327 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1950242251/10000000000 : ℝ), (5248050787/10000000000 : ℝ), (675785189/1250000000 : ℝ)] ![(5952268007299/50000000000000 : ℝ), (5399508360011/12500000000000 : ℝ), (22449698546327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1950242251/10000000000 : ℝ)|^4415 ≤ (5952268007299/50000000000000 : ℝ)^3391
        have hw : |(-1950242251/10000000000 : ℝ)|=(1950242251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5248050787/10000000000 : ℝ)|^4415 ≤ (5399508360011/12500000000000 : ℝ)^3391
        have hw : |(5248050787/10000000000 : ℝ)|=(5248050787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675785189/1250000000 : ℝ)|^4415 ≤ (22449698546327/50000000000000 : ℝ)^3391
        have hw : |(675785189/1250000000 : ℝ)|=(675785189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s7_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297941129/10000000000 : ℝ)*x 0 + (894767311/2000000000 : ℝ)*x 1 + (4128269219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297941129/10000000000 : ℝ)^4415 ≤ (16652674560673/50000000000000 : ℝ)^3391 := by
    have hnat : (4297941129 : ℕ)^4415*50000000000000^3391 ≤ 16652674560673^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297941129 10000000000 16652674560673 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894767311/2000000000 : ℝ)^4415 ≤ (35090855416851/100000000000000 : ℝ)^3391 := by
    have hnat : (894767311 : ℕ)^4415*100000000000000^3391 ≤ 35090855416851^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894767311 2000000000 35090855416851 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128269219/10000000000 : ℝ)^4415 ≤ (15801897724767/50000000000000 : ℝ)^3391 := by
    have hnat : (4128269219 : ℕ)^4415*50000000000000^3391 ≤ 15801897724767^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128269219 10000000000 15801897724767 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297941129/10000000000 : ℝ), (894767311/2000000000 : ℝ), (4128269219/10000000000 : ℝ)] ![(16652674560673/50000000000000 : ℝ), (35090855416851/100000000000000 : ℝ), (15801897724767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297941129/10000000000 : ℝ)|^4415 ≤ (16652674560673/50000000000000 : ℝ)^3391
        have hw : |(4297941129/10000000000 : ℝ)|=(4297941129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894767311/2000000000 : ℝ)|^4415 ≤ (35090855416851/100000000000000 : ℝ)^3391
        have hw : |(894767311/2000000000 : ℝ)|=(894767311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128269219/10000000000 : ℝ)|^4415 ≤ (15801897724767/50000000000000 : ℝ)^3391
        have hw : |(4128269219/10000000000 : ℝ)|=(4128269219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (356/3125 : ℝ) ^ (2207/512 : ℝ) ≤ (1072358476274557/12500000000000000000 : ℝ) := by
    have hpowers : (356/3125 : ℝ)^2207 ≤ (1072358476274557/12500000000000000000 : ℝ)^512 := by
      have hnat : (356 : ℕ)^2207*12500000000000000000^512 ≤ 1072358476274557^512*3125^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        356 3125 1072358476274557 12500000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (356/3125 : ℝ)) (X := (1072358476274557/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (2207/512 : ℝ) ≤ (1642312154708187/6250000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^2207 ≤ (1642312154708187/6250000000000000000 : ℝ)^512 := by
      have hnat : (1477 : ℕ)^2207*6250000000000000000^512 ≤ 1642312154708187^512*10000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 1642312154708187 6250000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (1642312154708187/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251072358476274557/6250000000000000000 : ℝ) ≤ (312512437955791/312500000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (6251072358476274557/6250000000000000000 : ℝ)^512 ≤ (312512437955791/312500000000000 : ℝ)^2207 := by
      have hnat : (6251072358476274557 : ℕ)^512*312500000000000^2207 ≤ 312512437955791^2207*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251072358476274557 6250000000000000000 312512437955791 312500000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312512437955791/312500000000000 : ℝ)) (X := (6251072358476274557/6250000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504356982785690931/12500000000000000000 : ℝ) ≤ (2000161701978207/2000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (12504356982785690931/12500000000000000000 : ℝ)^512 ≤ (2000161701978207/2000000000000000 : ℝ)^2207 := by
      have hnat : (12504356982785690931 : ℕ)^512*2000000000000000^2207 ≤ 2000161701978207^2207*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504356982785690931 12500000000000000000 2000161701978207 2000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000161701978207/2000000000000000 : ℝ)) (X := (12504356982785690931/12500000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126642312154708187/3125000000000000000 : ℝ) ≤ (5000609502598379/5000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (3126642312154708187/3125000000000000000 : ℝ)^512 ≤ (5000609502598379/5000000000000000 : ℝ)^2207 := by
      have hnat : (3126642312154708187 : ℕ)^512*5000000000000000^2207 ≤ 5000609502598379^2207*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126642312154708187 3125000000000000000 5000609502598379 5000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000609502598379/5000000000000000 : ℝ)) (X := (3126642312154708187/3125000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1072358476274557/12500000000000000000 : ℝ) ≤ ((527687371378493611/527812500000000000 : ℝ)+2*(410495305723/337800000000000 : ℝ)*(356/3125 : ℝ))^(2207/512 : ℝ) := by
    rw [show (527687371378493611/527812500000000000 : ℝ)+2*(410495305723/337800000000000 : ℝ)*(356/3125 : ℝ)=(312512437955791/312500000000000 : ℝ) by norm_num, show 1+2*(1072358476274557/12500000000000000000 : ℝ)=(6251072358476274557/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1642312154708187/6250000000000000000 : ℝ)+(1072358476274557/12500000000000000000 : ℝ) ≤ ((527687371378493611/527812500000000000 : ℝ)+(410495305723/337800000000000 : ℝ)*((1477/10000 : ℝ)+(356/3125 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (527687371378493611/527812500000000000 : ℝ)+(410495305723/337800000000000 : ℝ)*((1477/10000 : ℝ)+(356/3125 : ℝ))=(2000161701978207/2000000000000000 : ℝ) by norm_num, show 1+(1642312154708187/6250000000000000000 : ℝ)+(1072358476274557/12500000000000000000 : ℝ)=(12504356982785690931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1642312154708187/6250000000000000000 : ℝ) ≤ ((527687371378493611/527812500000000000 : ℝ)+2*(410495305723/337800000000000 : ℝ)*(1477/10000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (527687371378493611/527812500000000000 : ℝ)+2*(410495305723/337800000000000 : ℝ)*(1477/10000 : ℝ)=(5000609502598379/5000000000000000 : ℝ) by norm_num, show 1+2*(1642312154708187/6250000000000000000 : ℝ)=(3126642312154708187/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (527687371378493611/527812500000000000 : ℝ)*(X 1 0+X 2 0)+(410495305723/337800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (527687371378493611/527812500000000000 : ℝ)) (alpha := (410495305723/337800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (527687371378493611/527812500000000000 : ℝ)*(X 0 1+X 2 1)+(410495305723/337800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (527687371378493611/527812500000000000 : ℝ)) (alpha := (410495305723/337800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (527687371378493611/527812500000000000 : ℝ)*(X 0 2+X 1 2)+(410495305723/337800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (527687371378493611/527812500000000000 : ℝ)) (alpha := (410495305723/337800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1950230441/10000000000 : ℝ)*X 0 0+(337928799/625000000 : ℝ)*X 0 1+(1049495007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346762327/10000000000 : ℝ)*X 1 0+(-50783963/250000000 : ℝ)*X 1 1+(1311868761/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673381161/5000000000 : ℝ)*X 2 0+(5247475051/10000000000 : ℝ)*X 2 1+(-2031358517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148957869/5000000000 : ℝ)*X 0 0+(4127004223/10000000000 : ℝ)*X 0 1+(2237548093/5000000000 : ℝ)*X 0 2+(2148957869/5000000000 : ℝ)*X 1 0+(4127004223/10000000000 : ℝ)*X 1 1+(2237548093/5000000000 : ℝ)*X 1 2+(2148957869/5000000000 : ℝ)*X 2 0+(4127004223/10000000000 : ℝ)*X 2 1+(2237548093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1950242251/10000000000 : ℝ)*X 0 0+(5248050787/10000000000 : ℝ)*X 0 1+(675785189/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4297941129/10000000000 : ℝ)*X 0 0+(894767311/2000000000 : ℝ)*X 0 1+(4128269219/10000000000 : ℝ)*X 0 2+(4297941129/10000000000 : ℝ)*X 1 0+(894767311/2000000000 : ℝ)*X 1 1+(4128269219/10000000000 : ℝ)*X 1 2+(4297941129/10000000000 : ℝ)*X 2 0+(894767311/2000000000 : ℝ)*X 2 1+(4128269219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20697728246492616512102001/8796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42633071/10000000000000 : ℝ)*(base19) + (203571467/50000000000000 : ℝ)*(base23) + (1780549/25000000000000 : ℝ)*(lower2) + (54597921/100000000000000 : ℝ)*(upper3) + (9527751/20000000000000 : ℝ)*(upper5) + (2286729675760683/50000000000000 : ℝ)*(major0) + (2286729675760683/50000000000000 : ℝ)*(major1) + (2286729675760683/50000000000000 : ℝ)*(major2) + (6274096396058819/100000000000000 : ℝ)*(sp0) + (6274105645876769/100000000000000 : ℝ)*(sp1) + (1254821133012909/20000000000000 : ℝ)*(sp2) + (287280821290611/10000000000000 : ℝ)*(sp3) + (483807433/5000000000000 : ℝ)*(sp4) + (2169750401/50000000000000 : ℝ)*(sp5) + (22443848065679/781250000000 : ℝ)*(f.failure) + (6274106072207479/100000000000000 : ℝ)*(f.sum) + (3613480067291/1407500000000000000000000000 : ℝ)*base66 + (33888791266131917/17593750000000000000000000000000 : ℝ)*base67 + (13818395318274333/17593750000000000000000000000000 : ℝ)*base70 + (278835838734961833/17593750000000000000000000000000 : ℝ)*base72 + (10413530235203/2815000000000000000000000000 : ℝ)*base73 + (80871611765555583/17593750000000000000000000000000 : ℝ)*base76 + (94636173459993083/17593750000000000000000000000000 : ℝ)*base78 + (10282952888725667/17593750000000000000000000000000 : ℝ)*base79 + (80400595069/87968750000000000000000000 : ℝ)*base81 + (481167/78125000000000000000 : ℝ)*base89 + (481167/78125000000000000000 : ℝ)*base91 + (481167/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1455_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1455_s8_0 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975114067/5000000000 : ℝ)*x 0 + (5406858971/10000000000 : ℝ)*x 1 + (209899143/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975114067/5000000000 : ℝ)^4415 ≤ (595221191041/5000000000000 : ℝ)^3391 := by
    have hnat : (975114067 : ℕ)^4415*5000000000000^3391 ≤ 595221191041^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975114067 5000000000 595221191041 5000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406858971/10000000000 : ℝ)^4415 ≤ (22452820618467/50000000000000 : ℝ)^3391 := by
    have hnat : (5406858971 : ℕ)^4415*50000000000000^3391 ≤ 22452820618467^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406858971 10000000000 22452820618467 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209899143/400000000 : ℝ)^4415 ≤ (5398741865731/12500000000000 : ℝ)^3391 := by
    have hnat : (209899143 : ℕ)^4415*12500000000000^3391 ≤ 5398741865731^3391*400000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209899143 400000000 5398741865731 12500000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975114067/5000000000 : ℝ), (5406858971/10000000000 : ℝ), (209899143/400000000 : ℝ)] ![(595221191041/5000000000000 : ℝ), (22452820618467/50000000000000 : ℝ), (5398741865731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975114067/5000000000 : ℝ)|^4415 ≤ (595221191041/5000000000000 : ℝ)^3391
        have hw : |(-975114067/5000000000 : ℝ)|=(975114067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406858971/10000000000 : ℝ)|^4415 ≤ (22452820618467/50000000000000 : ℝ)^3391
        have hw : |(5406858971/10000000000 : ℝ)|=(5406858971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209899143/400000000 : ℝ)|^4415 ≤ (5398741865731/12500000000000 : ℝ)^3391
        have hw : |(209899143/400000000 : ℝ)|=(209899143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s8_1 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673381249/5000000000 : ℝ)*x 0 + (-1015676731/5000000000 : ℝ)*x 1 + (524747867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673381249/5000000000 : ℝ)^4415 ≤ (22128446331071/50000000000000 : ℝ)^3391 := by
    have hnat : (2673381249 : ℕ)^4415*50000000000000^3391 ≤ 22128446331071^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673381249 5000000000 22128446331071 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015676731/5000000000 : ℝ)^4415 ≤ (12553171382529/100000000000000 : ℝ)^3391 := by
    have hnat : (1015676731 : ℕ)^4415*100000000000000^3391 ≤ 12553171382529^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015676731 5000000000 12553171382529 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524747867/1000000000 : ℝ)^4415 ≤ (43189935943873/100000000000000 : ℝ)^3391 := by
    have hnat : (524747867 : ℕ)^4415*100000000000000^3391 ≤ 43189935943873^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524747867 1000000000 43189935943873 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673381249/5000000000 : ℝ), (-1015676731/5000000000 : ℝ), (524747867/1000000000 : ℝ)] ![(22128446331071/50000000000000 : ℝ), (12553171382529/100000000000000 : ℝ), (43189935943873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673381249/5000000000 : ℝ)|^4415 ≤ (22128446331071/50000000000000 : ℝ)^3391
        have hw : |(2673381249/5000000000 : ℝ)|=(2673381249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015676731/5000000000 : ℝ)|^4415 ≤ (12553171382529/100000000000000 : ℝ)^3391
        have hw : |(-1015676731/5000000000 : ℝ)|=(1015676731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524747867/1000000000 : ℝ)|^4415 ≤ (43189935943873/100000000000000 : ℝ)^3391
        have hw : |(524747867/1000000000 : ℝ)|=(524747867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s8_2 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-975119899/5000000000 : ℝ)*x 0 + (524805473/1000000000 : ℝ)*x 1 + (5406279407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (975119899/5000000000 : ℝ)^4415 ≤ (238090330391/2000000000000 : ℝ)^3391 := by
    have hnat : (975119899 : ℕ)^4415*2000000000000^3391 ≤ 238090330391^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975119899 5000000000 238090330391 2000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524805473/1000000000 : ℝ)^4415 ≤ (345568873079/800000000000 : ℝ)^3391 := by
    have hnat : (524805473 : ℕ)^4415*800000000000^3391 ≤ 345568873079^3391*1000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524805473 1000000000 345568873079 800000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406279407/10000000000 : ℝ)^4415 ≤ (8979874866273/20000000000000 : ℝ)^3391 := by
    have hnat : (5406279407 : ℕ)^4415*20000000000000^3391 ≤ 8979874866273^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406279407 10000000000 8979874866273 20000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-975119899/5000000000 : ℝ), (524805473/1000000000 : ℝ), (5406279407/10000000000 : ℝ)] ![(238090330391/2000000000000 : ℝ), (345568873079/800000000000 : ℝ), (8979874866273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-975119899/5000000000 : ℝ)|^4415 ≤ (238090330391/2000000000000 : ℝ)^3391
        have hw : |(-975119899/5000000000 : ℝ)|=(975119899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524805473/1000000000 : ℝ)|^4415 ≤ (345568873079/800000000000 : ℝ)^3391
        have hw : |(524805473/1000000000 : ℝ)|=(524805473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406279407/10000000000 : ℝ)|^4415 ≤ (8979874866273/20000000000000 : ℝ)^3391
        have hw : |(5406279407/10000000000 : ℝ)|=(5406279407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s8_3 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212208997/400000000 : ℝ)*x 0 + (-18725523/100000000 : ℝ)*x 1 + (2703139849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212208997/400000000 : ℝ)^4415 ≤ (21904886681503/50000000000000 : ℝ)^3391 := by
    have hnat : (212208997 : ℕ)^4415*50000000000000^3391 ≤ 21904886681503^3391*400000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212208997 400000000 21904886681503 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18725523/100000000 : ℝ)^4415 ≤ (11290849143411/100000000000000 : ℝ)^3391 := by
    have hnat : (18725523 : ℕ)^4415*100000000000000^3391 ≤ 11290849143411^3391*100000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18725523 100000000 11290849143411 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703139849/5000000000 : ℝ)^4415 ≤ (22449688738969/50000000000000 : ℝ)^3391 := by
    have hnat : (2703139849 : ℕ)^4415*50000000000000^3391 ≤ 22449688738969^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703139849 5000000000 22449688738969 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212208997/400000000 : ℝ), (-18725523/100000000 : ℝ), (2703139849/5000000000 : ℝ)] ![(21904886681503/50000000000000 : ℝ), (11290849143411/100000000000000 : ℝ), (22449688738969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212208997/400000000 : ℝ)|^4415 ≤ (21904886681503/50000000000000 : ℝ)^3391
        have hw : |(212208997/400000000 : ℝ)|=(212208997/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18725523/100000000 : ℝ)|^4415 ≤ (11290849143411/100000000000000 : ℝ)^3391
        have hw : |(-18725523/100000000 : ℝ)|=(18725523/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703139849/5000000000 : ℝ)|^4415 ≤ (22449688738969/50000000000000 : ℝ)^3391
        have hw : |(2703139849/5000000000 : ℝ)|=(2703139849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s8_4 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652612247/5000000000 : ℝ)*x 0 + (675784967/1250000000 : ℝ)*x 1 + (-936276419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652612247/5000000000 : ℝ)^4415 ≤ (21904884364549/50000000000000 : ℝ)^3391 := by
    have hnat : (2652612247 : ℕ)^4415*50000000000000^3391 ≤ 21904884364549^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652612247 5000000000 21904884364549 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675784967/1250000000 : ℝ)^4415 ≤ (4489937788883/10000000000000 : ℝ)^3391 := by
    have hnat : (675784967 : ℕ)^4415*10000000000000^3391 ≤ 4489937788883^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675784967 1250000000 4489937788883 10000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936276419/5000000000 : ℝ)^4415 ≤ (11290853366963/100000000000000 : ℝ)^3391 := by
    have hnat : (936276419 : ℕ)^4415*100000000000000^3391 ≤ 11290853366963^3391*5000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936276419 5000000000 11290853366963 100000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652612247/5000000000 : ℝ), (675784967/1250000000 : ℝ), (-936276419/5000000000 : ℝ)] ![(21904884364549/50000000000000 : ℝ), (4489937788883/10000000000000 : ℝ), (11290853366963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652612247/5000000000 : ℝ)|^4415 ≤ (21904884364549/50000000000000 : ℝ)^3391
        have hw : |(2652612247/5000000000 : ℝ)|=(2652612247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675784967/1250000000 : ℝ)|^4415 ≤ (4489937788883/10000000000000 : ℝ)^3391
        have hw : |(675784967/1250000000 : ℝ)|=(675784967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-936276419/5000000000 : ℝ)|^4415 ≤ (11290853366963/100000000000000 : ℝ)^3391
        have hw : |(-936276419/5000000000 : ℝ)|=(936276419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1455_s8_5 (p : ℝ) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297940561/10000000000 : ℝ)*x 0 + (894766151/2000000000 : ℝ)*x 1 + (516034467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297940561/10000000000 : ℝ)^4415 ≤ (8326335847671/25000000000000 : ℝ)^3391 := by
    have hnat : (4297940561 : ℕ)^4415*25000000000000^3391 ≤ 8326335847671^3391*10000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297940561 10000000000 8326335847671 25000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894766151/2000000000 : ℝ)^4415 ≤ (701815923729/2000000000000 : ℝ)^3391 := by
    have hnat : (894766151 : ℕ)^4415*2000000000000^3391 ≤ 701815923729^3391*2000000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894766151 2000000000 701815923729 2000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516034467/1250000000 : ℝ)^4415 ≤ (15801930202969/50000000000000 : ℝ)^3391 := by
    have hnat : (516034467 : ℕ)^4415*50000000000000^3391 ≤ 15801930202969^3391*1250000000^4415 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516034467 1250000000 15801930202969 50000000000000 4415 3391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4415/1024 : ℝ)) 4415 3391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297940561/10000000000 : ℝ), (894766151/2000000000 : ℝ), (516034467/1250000000 : ℝ)] ![(8326335847671/25000000000000 : ℝ), (701815923729/2000000000000 : ℝ), (15801930202969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297940561/10000000000 : ℝ)|^4415 ≤ (8326335847671/25000000000000 : ℝ)^3391
        have hw : |(4297940561/10000000000 : ℝ)|=(4297940561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894766151/2000000000 : ℝ)|^4415 ≤ (701815923729/2000000000000 : ℝ)^3391
        have hw : |(894766151/2000000000 : ℝ)|=(894766151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516034467/1250000000 : ℝ)|^4415 ≤ (15801930202969/50000000000000 : ℝ)^3391
        have hw : |(516034467/1250000000 : ℝ)|=(516034467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1455_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (2207/512 : ℝ) ≤ (2145528596364567/25000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^2207 ≤ (2145528596364567/25000000000000000000 : ℝ)^512 := by
      have hnat : (11393 : ℕ)^2207*25000000000000000000^512 ≤ 2145528596364567^512*100000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 2145528596364567 25000000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (2145528596364567/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (2207/512 : ℝ) ≤ (1642312154708187/6250000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^2207 ≤ (1642312154708187/6250000000000000000 : ℝ)^512 := by
      have hnat : (1477 : ℕ)^2207*6250000000000000000^512 ≤ 1642312154708187^512*10000^2207 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 1642312154708187 6250000000000000000 2207 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (1642312154708187/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502145528596364567/12500000000000000000 : ℝ) ≤ (10000398165199493/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (12502145528596364567/12500000000000000000 : ℝ)^512 ≤ (10000398165199493/10000000000000000 : ℝ)^2207 := by
      have hnat : (12502145528596364567 : ℕ)^512*10000000000000000^2207 ≤ 10000398165199493^2207*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502145528596364567 12500000000000000000 10000398165199493 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000398165199493/10000000000000000 : ℝ)) (X := (12502145528596364567/12500000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001742955443039463/5000000000000000000 : ℝ) ≤ (10000808585187893/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (5001742955443039463/5000000000000000000 : ℝ)^512 ≤ (10000808585187893/10000000000000000 : ℝ)^2207 := by
      have hnat : (5001742955443039463 : ℕ)^512*10000000000000000^2207 ≤ 10000808585187893^2207*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001742955443039463 5000000000000000000 10000808585187893 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000808585187893/10000000000000000 : ℝ)) (X := (5001742955443039463/5000000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126642312154708187/3125000000000000000 : ℝ) ≤ (10001219005176293/10000000000000000 : ℝ) ^ (2207/512 : ℝ) := by
    have hpowers : (3126642312154708187/3125000000000000000 : ℝ)^512 ≤ (10001219005176293/10000000000000000 : ℝ)^2207 := by
      have hnat : (3126642312154708187 : ℕ)^512*10000000000000000^2207 ≤ 10001219005176293^2207*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126642312154708187 3125000000000000000 10001219005176293 10000000000000000 512 2207 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001219005176293/10000000000000000 : ℝ)) (X := (3126642312154708187/3125000000000000000 : ℝ)) (by norm_num) 2207 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2145528596364567/25000000000000000000 : ℝ) ≤ ((33761992774023005461/33770000000000000000 : ℝ)+2*(1026049971/844250000000 : ℝ)*(11393/100000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (33761992774023005461/33770000000000000000 : ℝ)+2*(1026049971/844250000000 : ℝ)*(11393/100000 : ℝ)=(10000398165199493/10000000000000000 : ℝ) by norm_num, show 1+2*(2145528596364567/25000000000000000000 : ℝ)=(12502145528596364567/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1642312154708187/6250000000000000000 : ℝ)+(2145528596364567/25000000000000000000 : ℝ) ≤ ((33761992774023005461/33770000000000000000 : ℝ)+(1026049971/844250000000 : ℝ)*((1477/10000 : ℝ)+(11393/100000 : ℝ)))^(2207/512 : ℝ) := by
    rw [show (33761992774023005461/33770000000000000000 : ℝ)+(1026049971/844250000000 : ℝ)*((1477/10000 : ℝ)+(11393/100000 : ℝ))=(10000808585187893/10000000000000000 : ℝ) by norm_num, show 1+(1642312154708187/6250000000000000000 : ℝ)+(2145528596364567/25000000000000000000 : ℝ)=(5001742955443039463/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1642312154708187/6250000000000000000 : ℝ) ≤ ((33761992774023005461/33770000000000000000 : ℝ)+2*(1026049971/844250000000 : ℝ)*(1477/10000 : ℝ))^(2207/512 : ℝ) := by
    rw [show (33761992774023005461/33770000000000000000 : ℝ)+2*(1026049971/844250000000 : ℝ)*(1477/10000 : ℝ)=(10001219005176293/10000000000000000 : ℝ) by norm_num, show 1+2*(1642312154708187/6250000000000000000 : ℝ)=(3126642312154708187/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33761992774023005461/33770000000000000000 : ℝ)*(X 1 0+X 2 0)+(1026049971/844250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (33761992774023005461/33770000000000000000 : ℝ)) (alpha := (1026049971/844250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33761992774023005461/33770000000000000000 : ℝ)*(X 0 1+X 2 1)+(1026049971/844250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (33761992774023005461/33770000000000000000 : ℝ)) (alpha := (1026049971/844250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33761992774023005461/33770000000000000000 : ℝ)*(X 0 2+X 1 2)+(1026049971/844250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2207/512 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (33761992774023005461/33770000000000000000 : ℝ)) (alpha := (1026049971/844250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-975114067/5000000000 : ℝ)*X 0 0+(5406858971/10000000000 : ℝ)*X 0 1+(209899143/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673381249/5000000000 : ℝ)*X 1 0+(-1015676731/5000000000 : ℝ)*X 1 1+(524747867/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-975119899/5000000000 : ℝ)*X 0 0+(524805473/1000000000 : ℝ)*X 0 1+(5406279407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s8_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((212208997/400000000 : ℝ)*X 1 0+(-18725523/100000000 : ℝ)*X 1 1+(2703139849/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s8_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2652612247/5000000000 : ℝ)*X 2 0+(675784967/1250000000 : ℝ)*X 2 1+(-936276419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s8_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4297940561/10000000000 : ℝ)*X 0 0+(894766151/2000000000 : ℝ)*X 0 1+(516034467/1250000000 : ℝ)*X 0 2+(4297940561/10000000000 : ℝ)*X 1 0+(894766151/2000000000 : ℝ)*X 1 1+(516034467/1250000000 : ℝ)*X 1 2+(4297940561/10000000000 : ℝ)*X 2 0+(894766151/2000000000 : ℝ)*X 2 1+(516034467/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1455_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4436943388219486394036937/3837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205337791/20000000000000 : ℝ)*(base19) + (6815693/2500000000000 : ℝ)*(base23) + (159343903/100000000000000 : ℝ)*(lower1) + (1680951/20000000000000 : ℝ)*(lower4) + (69144289/25000000000000 : ℝ)*(upper5) + (230350207966429/5000000000000 : ℝ)*(major0) + (230350207966429/5000000000000 : ℝ)*(major1) + (230350207966429/5000000000000 : ℝ)*(major2) + (1507509901/100000000000000 : ℝ)*(sp0) + (6550880719/20000000000000 : ℝ)*(sp1) + (1264024618547691/20000000000000 : ℝ)*(sp2) + (1264018163831161/20000000000000 : ℝ)*(sp3) + (1580031081905159/25000000000000 : ℝ)*(sp4) + (115755347194743/4000000000000 : ℝ)*(sp5) + (115755347194743/4000000000000 : ℝ)*(f.failure) + (1580031150062089/25000000000000 : ℝ)*(f.sum) + (1336018567273/3377000000000000000000000000 : ℝ)*base65 + (160318669020431231/168850000000000000000000000000000 : ℝ)*base68 + (278585483289331231/168850000000000000000000000000000 : ℝ)*base70 + (476853720681831231/168850000000000000000000000000000 : ℝ)*base72 + (1996360877939/675400000000000000000000000 : ℝ)*base74 + (2456312027132668769/168850000000000000000000000000000 : ℝ)*base75 + (240503949025481231/168850000000000000000000000000000 : ℝ)*base78 + (159207310984181231/168850000000000000000000000000000 : ℝ)*base80 + (25469318937/26382812500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1855939/400000000000000000000 : ℝ)*base89 + (1855939/400000000000000000000 : ℝ)*base91 + (1855939/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1455_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1455_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1455_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1455_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1455_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1455_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2207/512 : ℝ) ≤ p) (hpb : p ≤ (4415/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159197973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1455_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
