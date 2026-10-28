-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1270_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:10.812923+00:00
-- url     : https://prove2.me/submissions/65e29f3c-a9b3-4f6a-b1da-f3f8baf568bf

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
theorem support_rectangle_w1270_s3_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104067113/10000000000 : ℝ)*x 0 + (1083435961/2000000000 : ℝ)*x 1 + (2621390939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104067113/10000000000 : ℝ)^529 ≤ (12793190249293/100000000000000 : ℝ)^401 := by
    have hnat : (2104067113 : ℕ)^529*100000000000000^401 ≤ 12793190249293^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104067113 10000000000 12793190249293 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083435961/2000000000 : ℝ)^529 ≤ (8908880570137/20000000000000 : ℝ)^401 := by
    have hnat : (1083435961 : ℕ)^529*20000000000000^401 ≤ 8908880570137^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083435961 2000000000 8908880570137 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621390939/5000000000 : ℝ)^529 ≤ (21331203440459/50000000000000 : ℝ)^401 := by
    have hnat : (2621390939 : ℕ)^529*50000000000000^401 ≤ 21331203440459^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621390939 5000000000 21331203440459 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104067113/10000000000 : ℝ), (1083435961/2000000000 : ℝ), (2621390939/5000000000 : ℝ)] ![(12793190249293/100000000000000 : ℝ), (8908880570137/20000000000000 : ℝ), (21331203440459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104067113/10000000000 : ℝ)|^529 ≤ (12793190249293/100000000000000 : ℝ)^401
        have hw : |(-2104067113/10000000000 : ℝ)|=(2104067113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083435961/2000000000 : ℝ)|^529 ≤ (8908880570137/20000000000000 : ℝ)^401
        have hw : |(1083435961/2000000000 : ℝ)|=(1083435961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621390939/5000000000 : ℝ)|^529 ≤ (21331203440459/50000000000000 : ℝ)^401
        have hw : |(2621390939/5000000000 : ℝ)|=(2621390939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (668857377/1250000000 : ℝ)*x 0 + (-1096494183/5000000000 : ℝ)*x 1 + (1048556403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668857377/1250000000 : ℝ)^529 ≤ (43826395182147/100000000000000 : ℝ)^401 := by
    have hnat : (668857377 : ℕ)^529*100000000000000^401 ≤ 43826395182147^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668857377 1250000000 43826395182147 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096494183/5000000000 : ℝ)^529 ≤ (6755598229631/50000000000000 : ℝ)^401 := by
    have hnat : (1096494183 : ℕ)^529*50000000000000^401 ≤ 6755598229631^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096494183 5000000000 6755598229631 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048556403/2000000000 : ℝ)^529 ≤ (42662408351589/100000000000000 : ℝ)^401 := by
    have hnat : (1048556403 : ℕ)^529*100000000000000^401 ≤ 42662408351589^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048556403 2000000000 42662408351589 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668857377/1250000000 : ℝ), (-1096494183/5000000000 : ℝ), (1048556403/2000000000 : ℝ)] ![(43826395182147/100000000000000 : ℝ), (6755598229631/50000000000000 : ℝ), (42662408351589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668857377/1250000000 : ℝ)|^529 ≤ (43826395182147/100000000000000 : ℝ)^401
        have hw : |(668857377/1250000000 : ℝ)|=(668857377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096494183/5000000000 : ℝ)|^529 ≤ (6755598229631/50000000000000 : ℝ)^401
        have hw : |(-1096494183/5000000000 : ℝ)|=(1096494183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048556403/2000000000 : ℝ)|^529 ≤ (42662408351589/100000000000000 : ℝ)^401
        have hw : |(1048556403/2000000000 : ℝ)|=(1048556403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5350859009/10000000000 : ℝ)*x 0 + (5242782469/10000000000 : ℝ)*x 1 + (-87719511/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350859009/10000000000 : ℝ)^529 ≤ (2739149694157/6250000000000 : ℝ)^401 := by
    have hnat : (5350859009 : ℕ)^529*6250000000000^401 ≤ 2739149694157^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350859009 10000000000 2739149694157 6250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242782469/10000000000 : ℝ)^529 ≤ (42662413225199/100000000000000 : ℝ)^401 := by
    have hnat : (5242782469 : ℕ)^529*100000000000000^401 ≤ 42662413225199^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242782469 10000000000 42662413225199 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87719511/400000000 : ℝ)^529 ≤ (13511191655779/100000000000000 : ℝ)^401 := by
    have hnat : (87719511 : ℕ)^529*100000000000000^401 ≤ 13511191655779^401*400000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87719511 400000000 13511191655779 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350859009/10000000000 : ℝ), (5242782469/10000000000 : ℝ), (-87719511/400000000 : ℝ)] ![(2739149694157/6250000000000 : ℝ), (42662413225199/100000000000000 : ℝ), (13511191655779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350859009/10000000000 : ℝ)|^529 ≤ (2739149694157/6250000000000 : ℝ)^401
        have hw : |(5350859009/10000000000 : ℝ)|=(5350859009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242782469/10000000000 : ℝ)|^529 ≤ (42662413225199/100000000000000 : ℝ)^401
        have hw : |(5242782469/10000000000 : ℝ)|=(5242782469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87719511/400000000 : ℝ)|^529 ≤ (13511191655779/100000000000000 : ℝ)^401
        have hw : |(-87719511/400000000 : ℝ)|=(87719511/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (869049437/2000000000 : ℝ)*x 0 + (4170880847/10000000000 : ℝ)*x 1 + (2263319781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869049437/2000000000 : ℝ)^529 ≤ (16650910761711/50000000000000 : ℝ)^401 := by
    have hnat : (869049437 : ℕ)^529*50000000000000^401 ≤ 16650910761711^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869049437 2000000000 16650910761711 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4170880847/10000000000 : ℝ)^529 ≤ (31550317491201/100000000000000 : ℝ)^401 := by
    have hnat : (4170880847 : ℕ)^529*100000000000000^401 ≤ 31550317491201^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170880847 10000000000 31550317491201 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263319781/5000000000 : ℝ)^529 ≤ (35147860983789/100000000000000 : ℝ)^401 := by
    have hnat : (2263319781 : ℕ)^529*100000000000000^401 ≤ 35147860983789^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263319781 5000000000 35147860983789 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869049437/2000000000 : ℝ), (4170880847/10000000000 : ℝ), (2263319781/5000000000 : ℝ)] ![(16650910761711/50000000000000 : ℝ), (31550317491201/100000000000000 : ℝ), (35147860983789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869049437/2000000000 : ℝ)|^529 ≤ (16650910761711/50000000000000 : ℝ)^401
        have hw : |(869049437/2000000000 : ℝ)|=(869049437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4170880847/10000000000 : ℝ)|^529 ≤ (31550317491201/100000000000000 : ℝ)^401
        have hw : |(4170880847/10000000000 : ℝ)|=(4170880847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263319781/5000000000 : ℝ)|^529 ≤ (35147860983789/100000000000000 : ℝ)^401
        have hw : |(2263319781/5000000000 : ℝ)|=(2263319781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104080879/10000000000 : ℝ)*x 0 + (1048680919/2000000000 : ℝ)*x 1 + (5416553357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104080879/10000000000 : ℝ)^529 ≤ (12793300667017/100000000000000 : ℝ)^401 := by
    have hnat : (2104080879 : ℕ)^529*100000000000000^401 ≤ 12793300667017^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104080879 10000000000 12793300667017 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048680919/2000000000 : ℝ)^529 ≤ (10667272941007/25000000000000 : ℝ)^401 := by
    have hnat : (1048680919 : ℕ)^529*25000000000000^401 ≤ 10667272941007^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048680919 2000000000 10667272941007 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416553357/10000000000 : ℝ)^529 ≤ (44537607557469/100000000000000 : ℝ)^401 := by
    have hnat : (5416553357 : ℕ)^529*100000000000000^401 ≤ 44537607557469^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416553357 10000000000 44537607557469 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104080879/10000000000 : ℝ), (1048680919/2000000000 : ℝ), (5416553357/10000000000 : ℝ)] ![(12793300667017/100000000000000 : ℝ), (10667272941007/25000000000000 : ℝ), (44537607557469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104080879/10000000000 : ℝ)|^529 ≤ (12793300667017/100000000000000 : ℝ)^401
        have hw : |(-2104080879/10000000000 : ℝ)|=(2104080879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048680919/2000000000 : ℝ)|^529 ≤ (10667272941007/25000000000000 : ℝ)^401
        have hw : |(1048680919/2000000000 : ℝ)|=(1048680919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416553357/10000000000 : ℝ)|^529 ≤ (44537607557469/100000000000000 : ℝ)^401
        have hw : |(5416553357/10000000000 : ℝ)|=(5416553357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1326570299/2500000000 : ℝ)*x 0 + (-403843247/2000000000 : ℝ)*x 1 + (677069149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326570299/2500000000 : ℝ)^529 ≤ (43345374848331/100000000000000 : ℝ)^401 := by
    have hnat : (1326570299 : ℕ)^529*100000000000000^401 ≤ 43345374848331^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326570299 2500000000 43345374848331 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403843247/2000000000 : ℝ)^529 ≤ (6058509688483/50000000000000 : ℝ)^401 := by
    have hnat : (403843247 : ℕ)^529*50000000000000^401 ≤ 6058509688483^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403843247 2000000000 6058509688483 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677069149/1250000000 : ℝ)^529 ≤ (11134401441923/25000000000000 : ℝ)^401 := by
    have hnat : (677069149 : ℕ)^529*25000000000000^401 ≤ 11134401441923^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677069149 1250000000 11134401441923 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326570299/2500000000 : ℝ), (-403843247/2000000000 : ℝ), (677069149/1250000000 : ℝ)] ![(43345374848331/100000000000000 : ℝ), (6058509688483/50000000000000 : ℝ), (11134401441923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326570299/2500000000 : ℝ)|^529 ≤ (43345374848331/100000000000000 : ℝ)^401
        have hw : |(1326570299/2500000000 : ℝ)|=(1326570299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403843247/2000000000 : ℝ)|^529 ≤ (6058509688483/50000000000000 : ℝ)^401
        have hw : |(-403843247/2000000000 : ℝ)|=(403843247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677069149/1250000000 : ℝ)|^529 ≤ (11134401441923/25000000000000 : ℝ)^401
        have hw : |(677069149/1250000000 : ℝ)|=(677069149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2653140243/5000000000 : ℝ)*x 0 + (2708276817/5000000000 : ℝ)*x 1 + (-403843319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2653140243/5000000000 : ℝ)^529 ≤ (21672683598631/50000000000000 : ℝ)^401 := by
    have hnat : (2653140243 : ℕ)^529*50000000000000^401 ≤ 21672683598631^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2653140243 5000000000 21672683598631 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708276817/5000000000 : ℝ)^529 ≤ (44537610562127/100000000000000 : ℝ)^401 := by
    have hnat : (2708276817 : ℕ)^529*100000000000000^401 ≤ 44537610562127^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708276817 5000000000 44537610562127 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403843319/2000000000 : ℝ)^529 ≤ (378656944589/3125000000000 : ℝ)^401 := by
    have hnat : (403843319 : ℕ)^529*3125000000000^401 ≤ 378656944589^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403843319 2000000000 378656944589 3125000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2653140243/5000000000 : ℝ), (2708276817/5000000000 : ℝ), (-403843319/2000000000 : ℝ)] ![(21672683598631/50000000000000 : ℝ), (44537610562127/100000000000000 : ℝ), (378656944589/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2653140243/5000000000 : ℝ)|^529 ≤ (21672683598631/50000000000000 : ℝ)^401
        have hw : |(2653140243/5000000000 : ℝ)|=(2653140243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708276817/5000000000 : ℝ)|^529 ≤ (44537610562127/100000000000000 : ℝ)^401
        have hw : |(2708276817/5000000000 : ℝ)|=(2708276817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403843319/2000000000 : ℝ)|^529 ≤ (378656944589/3125000000000 : ℝ)^401
        have hw : |(-403843319/2000000000 : ℝ)|=(403843319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4345274509/10000000000 : ℝ)*x 0 + (4525368437/10000000000 : ℝ)*x 1 + (834431563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345274509/10000000000 : ℝ)^529 ≤ (33302097778019/100000000000000 : ℝ)^401 := by
    have hnat : (4345274509 : ℕ)^529*100000000000000^401 ≤ 33302097778019^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345274509 10000000000 33302097778019 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525368437/10000000000 : ℝ)^529 ≤ (35134841220773/100000000000000 : ℝ)^401 := by
    have hnat : (4525368437 : ℕ)^529*100000000000000^401 ≤ 35134841220773^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525368437 10000000000 35134841220773 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834431563/2000000000 : ℝ)^529 ≤ (7890765246043/25000000000000 : ℝ)^401 := by
    have hnat : (834431563 : ℕ)^529*25000000000000^401 ≤ 7890765246043^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834431563 2000000000 7890765246043 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345274509/10000000000 : ℝ), (4525368437/10000000000 : ℝ), (834431563/2000000000 : ℝ)] ![(33302097778019/100000000000000 : ℝ), (35134841220773/100000000000000 : ℝ), (7890765246043/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345274509/10000000000 : ℝ)|^529 ≤ (33302097778019/100000000000000 : ℝ)^401
        have hw : |(4345274509/10000000000 : ℝ)|=(4345274509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525368437/10000000000 : ℝ)|^529 ≤ (35134841220773/100000000000000 : ℝ)^401
        have hw : |(4525368437/10000000000 : ℝ)|=(4525368437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834431563/2000000000 : ℝ)|^529 ≤ (7890765246043/25000000000000 : ℝ)^401
        have hw : |(834431563/2000000000 : ℝ)|=(834431563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_8 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-15945689/10000000000 : ℝ)*x 0 + (591201313/1000000000 : ℝ)*x 1 + (369511797/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15945689/10000000000 : ℝ)^529 ≤ (2040428809/10000000000000 : ℝ)^401 := by
    have hnat : (15945689 : ℕ)^529*10000000000000^401 ≤ 2040428809^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15945689 10000000000 2040428809 10000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591201313/1000000000 : ℝ)^529 ≤ (49988818359913/100000000000000 : ℝ)^401 := by
    have hnat : (591201313 : ℕ)^529*100000000000000^401 ≤ 49988818359913^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591201313 1000000000 49988818359913 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369511797/625000000 : ℝ)^529 ≤ (49990777338813/100000000000000 : ℝ)^401 := by
    have hnat : (369511797 : ℕ)^529*100000000000000^401 ≤ 49990777338813^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369511797 625000000 49990777338813 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15945689/10000000000 : ℝ), (591201313/1000000000 : ℝ), (369511797/625000000 : ℝ)] ![(2040428809/10000000000000 : ℝ), (49988818359913/100000000000000 : ℝ), (49990777338813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15945689/10000000000 : ℝ)|^529 ≤ (2040428809/10000000000000 : ℝ)^401
        have hw : |(-15945689/10000000000 : ℝ)|=(15945689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(591201313/1000000000 : ℝ)|^529 ≤ (49988818359913/100000000000000 : ℝ)^401
        have hw : |(591201313/1000000000 : ℝ)|=(591201313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(369511797/625000000 : ℝ)|^529 ≤ (49990777338813/100000000000000 : ℝ)^401
        have hw : |(369511797/625000000 : ℝ)|=(369511797/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_9 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (490616329/5000000000 : ℝ)*x 0 + (-43690549/100000000 : ℝ)*x 1 + (6941580569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490616329/5000000000 : ℝ)^529 ≤ (73074125947/1562500000000 : ℝ)^401 := by
    have hnat : (490616329 : ℕ)^529*1562500000000^401 ≤ 73074125947^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490616329 5000000000 73074125947 1562500000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43690549/100000000 : ℝ)^529 ≤ (4192841913629/12500000000000 : ℝ)^401 := by
    have hnat : (43690549 : ℕ)^529*12500000000000^401 ≤ 4192841913629^401*100000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43690549 100000000 4192841913629 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6941580569/10000000000 : ℝ)^529 ≤ (7722565077979/12500000000000 : ℝ)^401 := by
    have hnat : (6941580569 : ℕ)^529*12500000000000^401 ≤ 7722565077979^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6941580569 10000000000 7722565077979 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(490616329/5000000000 : ℝ), (-43690549/100000000 : ℝ), (6941580569/10000000000 : ℝ)] ![(73074125947/1562500000000 : ℝ), (4192841913629/12500000000000 : ℝ), (7722565077979/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(490616329/5000000000 : ℝ)|^529 ≤ (73074125947/1562500000000 : ℝ)^401
        have hw : |(490616329/5000000000 : ℝ)|=(490616329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43690549/100000000 : ℝ)|^529 ≤ (4192841913629/12500000000000 : ℝ)^401
        have hw : |(-43690549/100000000 : ℝ)|=(43690549/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6941580569/10000000000 : ℝ)|^529 ≤ (7722565077979/12500000000000 : ℝ)^401
        have hw : |(6941580569/10000000000 : ℝ)|=(6941580569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s3_10 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (75281917/500000000 : ℝ)*x 0 + (579357079/1000000000 : ℝ)*x 1 + (2641793507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (75281917/500000000 : ℝ)^529 ≤ (8227112975161/100000000000000 : ℝ)^401 := by
    have hnat : (75281917 : ℕ)^529*100000000000000^401 ≤ 8227112975161^401*500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75281917 500000000 8227112975161 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579357079/1000000000 : ℝ)^529 ≤ (48671901065199/100000000000000 : ℝ)^401 := by
    have hnat : (579357079 : ℕ)^529*100000000000000^401 ≤ 48671901065199^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579357079 1000000000 48671901065199 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641793507/5000000000 : ℝ)^529 ≤ (538762324187/1250000000000 : ℝ)^401 := by
    have hnat : (2641793507 : ℕ)^529*1250000000000^401 ≤ 538762324187^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641793507 5000000000 538762324187 1250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(75281917/500000000 : ℝ), (579357079/1000000000 : ℝ), (2641793507/5000000000 : ℝ)] ![(8227112975161/100000000000000 : ℝ), (48671901065199/100000000000000 : ℝ), (538762324187/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(75281917/500000000 : ℝ)|^529 ≤ (8227112975161/100000000000000 : ℝ)^401
        have hw : |(75281917/500000000 : ℝ)|=(75281917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(579357079/1000000000 : ℝ)|^529 ≤ (48671901065199/100000000000000 : ℝ)^401
        have hw : |(579357079/1000000000 : ℝ)|=(579357079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641793507/5000000000 : ℝ)|^529 ≤ (538762324187/1250000000000 : ℝ)^401
        have hw : |(2641793507/5000000000 : ℝ)|=(2641793507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1373/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (587/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16149/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1923/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16149/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1923/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16149/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1923/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16149/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1923/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16149/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1923/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16149/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1923/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1923/20000 : ℝ) ^ (8463/2048 : ℝ) ≤ (6269266237869573/100000000000000000000 : ℝ) := by
    have hpowers : (1923/20000 : ℝ)^8463 ≤ (6269266237869573/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1923 : ℕ)^8463*100000000000000000000^2048 ≤ 6269266237869573^2048*20000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1923 20000 6269266237869573 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1923/20000 : ℝ)) (X := (6269266237869573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16149/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (13357987617195759/25000000000000000000 : ℝ) := by
    have hpowers : (16149/100000 : ℝ)^8463 ≤ (13357987617195759/25000000000000000000 : ℝ)^2048 := by
      have hnat : (16149 : ℕ)^8463*25000000000000000000^2048 ≤ 13357987617195759^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16149 100000 13357987617195759 25000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16149/100000 : ℝ)) (X := (13357987617195759/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006269266237869573/50000000000000000000 : ℝ) ≤ (10000303411252541/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50006269266237869573/50000000000000000000 : ℝ)^2048 ≤ (10000303411252541/10000000000000000 : ℝ)^8463 := by
      have hnat : (50006269266237869573 : ℕ)^2048*10000000000000000^8463 ≤ 10000303411252541^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006269266237869573 50000000000000000000 10000303411252541 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000303411252541/10000000000000000 : ℝ)) (X := (50006269266237869573/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100059701216706652609/100000000000000000000 : ℝ) ≤ (500072220510447/500000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (100059701216706652609/100000000000000000000 : ℝ)^2048 ≤ (500072220510447/500000000000000 : ℝ)^8463 := by
      have hnat : (100059701216706652609 : ℕ)^2048*500000000000000^8463 ≤ 500072220510447^8463*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100059701216706652609 100000000000000000000 500072220510447 500000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500072220510447/500000000000000 : ℝ)) (X := (100059701216706652609/100000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12513357987617195759/12500000000000000000 : ℝ) ≤ (10002585409165339/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (12513357987617195759/12500000000000000000 : ℝ)^2048 ≤ (10002585409165339/10000000000000000 : ℝ)^8463 := by
      have hnat : (12513357987617195759 : ℕ)^2048*10000000000000000^8463 ≤ 10002585409165339^8463*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12513357987617195759 12500000000000000000 10002585409165339 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002585409165339/10000000000000000 : ℝ)) (X := (12513357987617195759/12500000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6269266237869573/100000000000000000000 : ℝ) ≤ ((5443336756599379177/5445000000000000000 : ℝ)+2*(1140998956399/653400000000000 : ℝ)*(1923/20000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (5443336756599379177/5445000000000000000 : ℝ)+2*(1140998956399/653400000000000 : ℝ)*(1923/20000 : ℝ)=(10000303411252541/10000000000000000 : ℝ) by norm_num, show 1+2*(6269266237869573/100000000000000000000 : ℝ)=(50006269266237869573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13357987617195759/25000000000000000000 : ℝ)+(6269266237869573/100000000000000000000 : ℝ) ≤ ((5443336756599379177/5445000000000000000 : ℝ)+(1140998956399/653400000000000 : ℝ)*((16149/100000 : ℝ)+(1923/20000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (5443336756599379177/5445000000000000000 : ℝ)+(1140998956399/653400000000000 : ℝ)*((16149/100000 : ℝ)+(1923/20000 : ℝ))=(500072220510447/500000000000000 : ℝ) by norm_num, show 1+(13357987617195759/25000000000000000000 : ℝ)+(6269266237869573/100000000000000000000 : ℝ)=(100059701216706652609/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13357987617195759/25000000000000000000 : ℝ) ≤ ((5443336756599379177/5445000000000000000 : ℝ)+2*(1140998956399/653400000000000 : ℝ)*(16149/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (5443336756599379177/5445000000000000000 : ℝ)+2*(1140998956399/653400000000000 : ℝ)*(16149/100000 : ℝ)=(10002585409165339/10000000000000000 : ℝ) by norm_num, show 1+2*(13357987617195759/25000000000000000000 : ℝ)=(12513357987617195759/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5443336756599379177/5445000000000000000 : ℝ)*(X 1 0+X 2 0)+(1140998956399/653400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (1923/20000 : ℝ)) (hi := (16149/100000 : ℝ)) (c := (5443336756599379177/5445000000000000000 : ℝ)) (alpha := (1140998956399/653400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5443336756599379177/5445000000000000000 : ℝ)*(X 0 1+X 2 1)+(1140998956399/653400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (1923/20000 : ℝ)) (hi := (16149/100000 : ℝ)) (c := (5443336756599379177/5445000000000000000 : ℝ)) (alpha := (1140998956399/653400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5443336756599379177/5445000000000000000 : ℝ)*(X 0 2+X 1 2)+(1140998956399/653400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (1923/20000 : ℝ)) (hi := (16149/100000 : ℝ)) (c := (5443336756599379177/5445000000000000000 : ℝ)) (alpha := (1140998956399/653400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2104067113/10000000000 : ℝ)*X 0 0+(1083435961/2000000000 : ℝ)*X 0 1+(2621390939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668857377/1250000000 : ℝ)*X 1 0+(-1096494183/5000000000 : ℝ)*X 1 1+(1048556403/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350859009/10000000000 : ℝ)*X 2 0+(5242782469/10000000000 : ℝ)*X 2 1+(-87719511/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869049437/2000000000 : ℝ)*X 0 0+(4170880847/10000000000 : ℝ)*X 0 1+(2263319781/5000000000 : ℝ)*X 0 2+(869049437/2000000000 : ℝ)*X 1 0+(4170880847/10000000000 : ℝ)*X 1 1+(2263319781/5000000000 : ℝ)*X 1 2+(869049437/2000000000 : ℝ)*X 2 0+(4170880847/10000000000 : ℝ)*X 2 1+(2263319781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2104080879/10000000000 : ℝ)*X 0 0+(1048680919/2000000000 : ℝ)*X 0 1+(5416553357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326570299/2500000000 : ℝ)*X 1 0+(-403843247/2000000000 : ℝ)*X 1 1+(677069149/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2653140243/5000000000 : ℝ)*X 2 0+(2708276817/5000000000 : ℝ)*X 2 1+(-403843319/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345274509/10000000000 : ℝ)*X 0 0+(4525368437/10000000000 : ℝ)*X 0 1+(834431563/2000000000 : ℝ)*X 0 2+(4345274509/10000000000 : ℝ)*X 1 0+(4525368437/10000000000 : ℝ)*X 1 1+(834431563/2000000000 : ℝ)*X 1 2+(4345274509/10000000000 : ℝ)*X 2 0+(4525368437/10000000000 : ℝ)*X 2 1+(834431563/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-15945689/10000000000 : ℝ)*X 0 0+(591201313/1000000000 : ℝ)*X 0 1+(369511797/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((490616329/5000000000 : ℝ)*X 1 0+(-43690549/100000000 : ℝ)*X 1 1+(6941580569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((75281917/500000000 : ℝ)*X 0 0+(579357079/1000000000 : ℝ)*X 0 1+(2641793507/5000000000 : ℝ)*X 0 2+(75281917/500000000 : ℝ)*X 1 0+(579357079/1000000000 : ℝ)*X 1 1+(2641793507/5000000000 : ℝ)*X 1 2+(75281917/500000000 : ℝ)*X 2 0+(579357079/1000000000 : ℝ)*X 2 1+(2641793507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s3_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1446127152708767597934195271/272250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24153249/25000000000000 : ℝ)*(lower2) + (33224149/20000000000000 : ℝ)*(lower3) + (423587/1000000000000 : ℝ)*(lower4) + (4272481007761541/100000000000000 : ℝ)*(major0) + (4272481007761541/100000000000000 : ℝ)*(major1) + (4272481007761541/100000000000000 : ℝ)*(major2) + (5734032445933423/100000000000000 : ℝ)*(sp0) + (1433511631580091/25000000000000 : ℝ)*(sp1) + (2867029798713221/50000000000000 : ℝ)*(sp2) + (1405449454402993/50000000000000 : ℝ)*(sp3) + (1357574651/5000000000000 : ℝ)*(sp4) + (13071106079/100000000000000 : ℝ)*(sp5) + (1465061669/50000000000000 : ℝ)*(sp7) + (20105429/5000000000000 : ℝ)*(sp10) + (2810902241037903/100000000000000 : ℝ)*(f.failure) + (2867029798713221/50000000000000 : ℝ)*(f.sum) + (11758015081949/32670000000000000000000000000 : ℝ)*base65 + (2033061347868529729/1633500000000000000000000000000000 : ℝ)*base68 + (7609014893234029729/1633500000000000000000000000000000 : ℝ)*base70 + (2877681518781970271/1633500000000000000000000000000000 : ℝ)*base71 + (144401905520671/32670000000000000000000000000 : ℝ)*base74 + (13724072935283029729/1633500000000000000000000000000000 : ℝ)*base76 + (48508510096163029729/1633500000000000000000000000000000 : ℝ)*base78 + (11024981027250970271/1633500000000000000000000000000000 : ℝ)*base79 + (60070995028381/32670000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1368503/625000000000000000000 : ℝ)*base90 + (1368503/625000000000000000000 : ℝ)*base92 + (1368503/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25806270197170940516811617/12375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5038967/2500000000000 : ℝ)*(lower3) + (2151641350160977/50000000000000 : ℝ)*(major0) + (2151641350160977/50000000000000 : ℝ)*(major1) + (2151641350160977/50000000000000 : ℝ)*(major2) + (3051143399/50000000000000 : ℝ)*(sp0) + (15684452891/100000000000000 : ℝ)*(sp1) + (14094205613/100000000000000 : ℝ)*(sp2) + (1155078107107287/20000000000000 : ℝ)*(sp4) + (5775381740983883/100000000000000 : ℝ)*(sp5) + (2887692147854411/50000000000000 : ℝ)*(sp6) + (1415582795437539/50000000000000 : ℝ)*(sp7) + (876045601/50000000000000 : ℝ)*(sp8) + (482238831/50000000000000 : ℝ)*(sp9) + (1350342543/100000000000000 : ℝ)*(sp10) + (2831166941217621/100000000000000 : ℝ)*(f.failure) + (1155079677982887/20000000000000 : ℝ)*(f.sum) + (7741721274787/4083750000000000000000000000 : ℝ)*base65 + (5815581688263347213/816750000000000000000000000000000 : ℝ)*base68 + (38828551175429652787/816750000000000000000000000000000 : ℝ)*base69 + (4662986302472597213/816750000000000000000000000000000 : ℝ)*base72 + (11838437017687/4083750000000000000000000000 : ℝ)*base73 + (8426023495698347213/816750000000000000000000000000000 : ℝ)*base76 + (2578645824836652787/816750000000000000000000000000000 : ℝ)*base77 + (6659808930610847213/816750000000000000000000000000000 : ℝ)*base80 + (248661219156239/8167500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2258179/625000000000000000000 : ℝ)*base89 + (2258179/625000000000000000000 : ℝ)*base91 + (2258179/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1270_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (587/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1270_s4_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106186859/10000000000 : ℝ)*x 0 + (5396346557/10000000000 : ℝ)*x 1 + (5262225319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106186859/10000000000 : ℝ)^529 ≤ (6405097772781/50000000000000 : ℝ)^401 := by
    have hnat : (2106186859 : ℕ)^529*50000000000000^401 ≤ 6405097772781^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106186859 10000000000 6405097772781 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396346557/10000000000 : ℝ)^529 ≤ (22159276113717/50000000000000 : ℝ)^401 := by
    have hnat : (5396346557 : ℕ)^529*50000000000000^401 ≤ 22159276113717^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396346557 10000000000 22159276113717 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262225319/10000000000 : ℝ)^529 ≤ (42871252204901/100000000000000 : ℝ)^401 := by
    have hnat : (5262225319 : ℕ)^529*100000000000000^401 ≤ 42871252204901^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262225319 10000000000 42871252204901 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106186859/10000000000 : ℝ), (5396346557/10000000000 : ℝ), (5262225319/10000000000 : ℝ)] ![(6405097772781/50000000000000 : ℝ), (22159276113717/50000000000000 : ℝ), (42871252204901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106186859/10000000000 : ℝ)|^529 ≤ (6405097772781/50000000000000 : ℝ)^401
        have hw : |(-2106186859/10000000000 : ℝ)|=(2106186859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396346557/10000000000 : ℝ)|^529 ≤ (22159276113717/50000000000000 : ℝ)^401
        have hw : |(5396346557/10000000000 : ℝ)|=(5396346557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262225319/10000000000 : ℝ)|^529 ≤ (42871252204901/100000000000000 : ℝ)^401
        have hw : |(5262225319/10000000000 : ℝ)|=(5262225319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5220306/9765625 : ℝ)*x 0 + (-1087133349/5000000000 : ℝ)*x 1 + (2631112631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5220306/9765625 : ℝ)^529 ≤ (5471188586911/12500000000000 : ℝ)^401 := by
    have hnat : (5220306 : ℕ)^529*12500000000000^401 ≤ 5471188586911^401*9765625^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220306 9765625 5471188586911 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087133349/5000000000 : ℝ)^529 ≤ (6679619849067/50000000000000 : ℝ)^401 := by
    have hnat : (1087133349 : ℕ)^529*50000000000000^401 ≤ 6679619849067^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087133349 5000000000 6679619849067 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631112631/5000000000 : ℝ)^529 ≤ (42871251592293/100000000000000 : ℝ)^401 := by
    have hnat : (2631112631 : ℕ)^529*100000000000000^401 ≤ 42871251592293^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631112631 5000000000 42871251592293 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5220306/9765625 : ℝ), (-1087133349/5000000000 : ℝ), (2631112631/5000000000 : ℝ)] ![(5471188586911/12500000000000 : ℝ), (6679619849067/50000000000000 : ℝ), (42871251592293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5220306/9765625 : ℝ)|^529 ≤ (5471188586911/12500000000000 : ℝ)^401
        have hw : |(5220306/9765625 : ℝ)|=(5220306/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087133349/5000000000 : ℝ)|^529 ≤ (6679619849067/50000000000000 : ℝ)^401
        have hw : |(-1087133349/5000000000 : ℝ)|=(1087133349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631112631/5000000000 : ℝ)|^529 ≤ (42871251592293/100000000000000 : ℝ)^401
        have hw : |(2631112631/5000000000 : ℝ)|=(2631112631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345593557/10000000000 : ℝ)*x 0 + (5262225127/10000000000 : ℝ)*x 1 + (-2174266593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345593557/10000000000 : ℝ)^529 ≤ (5471188874503/12500000000000 : ℝ)^401 := by
    have hnat : (5345593557 : ℕ)^529*12500000000000^401 ≤ 5471188874503^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345593557 10000000000 5471188874503 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262225127/10000000000 : ℝ)^529 ≤ (42871250141379/100000000000000 : ℝ)^401 := by
    have hnat : (5262225127 : ℕ)^529*100000000000000^401 ≤ 42871250141379^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262225127 10000000000 42871250141379 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174266593/10000000000 : ℝ)^529 ≤ (834952427941/6250000000000 : ℝ)^401 := by
    have hnat : (2174266593 : ℕ)^529*6250000000000^401 ≤ 834952427941^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174266593 10000000000 834952427941 6250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345593557/10000000000 : ℝ), (5262225127/10000000000 : ℝ), (-2174266593/10000000000 : ℝ)] ![(5471188874503/12500000000000 : ℝ), (42871250141379/100000000000000 : ℝ), (834952427941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345593557/10000000000 : ℝ)|^529 ≤ (5471188874503/12500000000000 : ℝ)^401
        have hw : |(5345593557/10000000000 : ℝ)|=(5345593557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262225127/10000000000 : ℝ)|^529 ≤ (42871250141379/100000000000000 : ℝ)^401
        have hw : |(5262225127/10000000000 : ℝ)|=(5262225127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174266593/10000000000 : ℝ)|^529 ≤ (834952427941/6250000000000 : ℝ)^401
        have hw : |(-2174266593/10000000000 : ℝ)|=(2174266593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (543314949/1250000000 : ℝ)*x 0 + (2105899603/5000000000 : ℝ)*x 1 + (1121349529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543314949/1250000000 : ℝ)^529 ≤ (33314686563583/100000000000000 : ℝ)^401 := by
    have hnat : (543314949 : ℕ)^529*100000000000000^401 ≤ 33314686563583^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543314949 1250000000 33314686563583 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105899603/5000000000 : ℝ)^529 ≤ (31959279931471/100000000000000 : ℝ)^401 := by
    have hnat : (2105899603 : ℕ)^529*100000000000000^401 ≤ 31959279931471^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105899603 5000000000 31959279931471 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121349529/2500000000 : ℝ)^529 ≤ (17363016741477/50000000000000 : ℝ)^401 := by
    have hnat : (1121349529 : ℕ)^529*50000000000000^401 ≤ 17363016741477^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121349529 2500000000 17363016741477 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543314949/1250000000 : ℝ), (2105899603/5000000000 : ℝ), (1121349529/2500000000 : ℝ)] ![(33314686563583/100000000000000 : ℝ), (31959279931471/100000000000000 : ℝ), (17363016741477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543314949/1250000000 : ℝ)|^529 ≤ (33314686563583/100000000000000 : ℝ)^401
        have hw : |(543314949/1250000000 : ℝ)|=(543314949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2105899603/5000000000 : ℝ)|^529 ≤ (31959279931471/100000000000000 : ℝ)^401
        have hw : |(2105899603/5000000000 : ℝ)|=(2105899603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121349529/2500000000 : ℝ)|^529 ≤ (17363016741477/50000000000000 : ℝ)^401
        have hw : |(1121349529/2500000000 : ℝ)|=(1121349529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-421238549/2000000000 : ℝ)*x 0 + (1315648517/2500000000 : ℝ)*x 1 + (674497049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (421238549/2000000000 : ℝ)^529 ≤ (1281024277259/10000000000000 : ℝ)^401 := by
    have hnat : (421238549 : ℕ)^529*10000000000000^401 ≤ 1281024277259^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421238549 2000000000 1281024277259 10000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315648517/2500000000 : ℝ)^529 ≤ (8575043076869/20000000000000 : ℝ)^401 := by
    have hnat : (1315648517 : ℕ)^529*20000000000000^401 ≤ 8575043076869^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315648517 2500000000 8575043076869 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674497049/1250000000 : ℝ)^529 ≤ (44314541828007/100000000000000 : ℝ)^401 := by
    have hnat : (674497049 : ℕ)^529*100000000000000^401 ≤ 44314541828007^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674497049 1250000000 44314541828007 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-421238549/2000000000 : ℝ), (1315648517/2500000000 : ℝ), (674497049/1250000000 : ℝ)] ![(1281024277259/10000000000000 : ℝ), (8575043076869/20000000000000 : ℝ), (44314541828007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-421238549/2000000000 : ℝ)|^529 ≤ (1281024277259/10000000000000 : ℝ)^401
        have hw : |(-421238549/2000000000 : ℝ)|=(421238549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315648517/2500000000 : ℝ)|^529 ≤ (8575043076869/20000000000000 : ℝ)^401
        have hw : |(1315648517/2500000000 : ℝ)|=(1315648517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674497049/1250000000 : ℝ)|^529 ≤ (44314541828007/100000000000000 : ℝ)^401
        have hw : |(674497049/1250000000 : ℝ)|=(674497049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5311307253/10000000000 : ℝ)*x 0 + (-2040515353/10000000000 : ℝ)*x 1 + (674497049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311307253/10000000000 : ℝ)^529 ≤ (10849886150027/25000000000000 : ℝ)^401 := by
    have hnat : (5311307253 : ℕ)^529*25000000000000^401 ≤ 10849886150027^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311307253 10000000000 10849886150027 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040515353/10000000000 : ℝ)^529 ≤ (12285913553219/100000000000000 : ℝ)^401 := by
    have hnat : (2040515353 : ℕ)^529*100000000000000^401 ≤ 12285913553219^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040515353 10000000000 12285913553219 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674497049/1250000000 : ℝ)^529 ≤ (44314541828007/100000000000000 : ℝ)^401 := by
    have hnat : (674497049 : ℕ)^529*100000000000000^401 ≤ 44314541828007^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674497049 1250000000 44314541828007 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311307253/10000000000 : ℝ), (-2040515353/10000000000 : ℝ), (674497049/1250000000 : ℝ)] ![(10849886150027/25000000000000 : ℝ), (12285913553219/100000000000000 : ℝ), (44314541828007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311307253/10000000000 : ℝ)|^529 ≤ (10849886150027/25000000000000 : ℝ)^401
        have hw : |(5311307253/10000000000 : ℝ)|=(5311307253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040515353/10000000000 : ℝ)|^529 ≤ (12285913553219/100000000000000 : ℝ)^401
        have hw : |(-2040515353/10000000000 : ℝ)|=(2040515353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674497049/1250000000 : ℝ)|^529 ≤ (44314541828007/100000000000000 : ℝ)^401
        have hw : |(674497049/1250000000 : ℝ)|=(674497049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5311307349/10000000000 : ℝ)*x 0 + (1348994067/2500000000 : ℝ)*x 1 + (-1020257697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311307349/10000000000 : ℝ)^529 ≤ (43399545634931/100000000000000 : ℝ)^401 := by
    have hnat : (5311307349 : ℕ)^529*100000000000000^401 ≤ 43399545634931^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311307349 10000000000 43399545634931 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348994067/2500000000 : ℝ)^529 ≤ (8862908096919/20000000000000 : ℝ)^401 := by
    have hnat : (1348994067 : ℕ)^529*20000000000000^401 ≤ 8862908096919^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348994067 2500000000 8862908096919 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020257697/5000000000 : ℝ)^529 ≤ (6142956939439/50000000000000 : ℝ)^401 := by
    have hnat : (1020257697 : ℕ)^529*50000000000000^401 ≤ 6142956939439^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020257697 5000000000 6142956939439 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311307349/10000000000 : ℝ), (1348994067/2500000000 : ℝ), (-1020257697/5000000000 : ℝ)] ![(43399545634931/100000000000000 : ℝ), (8862908096919/20000000000000 : ℝ), (6142956939439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311307349/10000000000 : ℝ)|^529 ≤ (43399545634931/100000000000000 : ℝ)^401
        have hw : |(5311307349/10000000000 : ℝ)|=(5311307349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348994067/2500000000 : ℝ)|^529 ≤ (8862908096919/20000000000000 : ℝ)^401
        have hw : |(1348994067/2500000000 : ℝ)|=(1348994067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020257697/5000000000 : ℝ)|^529 ≤ (6142956939439/50000000000000 : ℝ)^401
        have hw : |(-1020257697/5000000000 : ℝ)|=(1020257697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s4_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (869306409/2000000000 : ℝ)*x 0 + (2242322763/5000000000 : ℝ)*x 1 + (263284653/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869306409/2000000000 : ℝ)^529 ≤ (16657406239597/50000000000000 : ℝ)^401 := by
    have hnat : (869306409 : ℕ)^529*50000000000000^401 ≤ 16657406239597^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869306409 2000000000 16657406239597 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242322763/5000000000 : ℝ)^529 ≤ (1388733890883/4000000000000 : ℝ)^401 := by
    have hnat : (2242322763 : ℕ)^529*4000000000000^401 ≤ 1388733890883^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242322763 5000000000 1388733890883 4000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263284653/625000000 : ℝ)^529 ≤ (31966840234251/100000000000000 : ℝ)^401 := by
    have hnat : (263284653 : ℕ)^529*100000000000000^401 ≤ 31966840234251^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263284653 625000000 31966840234251 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869306409/2000000000 : ℝ), (2242322763/5000000000 : ℝ), (263284653/625000000 : ℝ)] ![(16657406239597/50000000000000 : ℝ), (1388733890883/4000000000000 : ℝ), (31966840234251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869306409/2000000000 : ℝ)|^529 ≤ (16657406239597/50000000000000 : ℝ)^401
        have hw : |(869306409/2000000000 : ℝ)|=(869306409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242322763/5000000000 : ℝ)|^529 ≤ (1388733890883/4000000000000 : ℝ)^401
        have hw : |(2242322763/5000000000 : ℝ)|=(2242322763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263284653/625000000 : ℝ)|^529 ≤ (31966840234251/100000000000000 : ℝ)^401
        have hw : |(263284653/625000000 : ℝ)|=(263284653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5699/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (587/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (587/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (587/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1373/12500 : ℝ) ^ (8463/2048 : ℝ) ≤ (10867045431103223/100000000000000000000 : ℝ) := by
    have hpowers : (1373/12500 : ℝ)^8463 ≤ (10867045431103223/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1373 : ℕ)^8463*100000000000000000000^2048 ≤ 10867045431103223^2048*12500^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1373 12500 10867045431103223 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1373/12500 : ℝ)) (X := (10867045431103223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (587/4000 : ℝ) ^ (8463/2048 : ℝ) ≤ (35977463328430139/100000000000000000000 : ℝ) := by
    have hpowers : (587/4000 : ℝ)^8463 ≤ (35977463328430139/100000000000000000000 : ℝ)^2048 := by
      have hnat : (587 : ℕ)^8463*100000000000000000000^2048 ≤ 35977463328430139^2048*4000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        587 4000 35977463328430139 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (587/4000 : ℝ)) (X := (35977463328430139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010867045431103223/50000000000000000000 : ℝ) ≤ (10000525909866747/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50010867045431103223/50000000000000000000 : ℝ)^2048 ≤ (10000525909866747/10000000000000000 : ℝ)^8463 := by
      have hnat : (50010867045431103223 : ℕ)^2048*10000000000000000^8463 ≤ 10000525909866747^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010867045431103223 50000000000000000000 10000525909866747 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000525909866747/10000000000000000 : ℝ)) (X := (50010867045431103223/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023422254379766681/50000000000000000000 : ℝ) ≤ (2500283352610399/2500000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50023422254379766681/50000000000000000000 : ℝ)^2048 ≤ (2500283352610399/2500000000000000 : ℝ)^8463 := by
      have hnat : (50023422254379766681 : ℕ)^2048*2500000000000000^8463 ≤ 2500283352610399^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023422254379766681 50000000000000000000 2500283352610399 2500000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500283352610399/2500000000000000 : ℝ)) (X := (50023422254379766681/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035977463328430139/50000000000000000000 : ℝ) ≤ (2000348182203289/2000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50035977463328430139/50000000000000000000 : ℝ)^2048 ≤ (2000348182203289/2000000000000000 : ℝ)^8463 := by
      have hnat : (50035977463328430139 : ℕ)^2048*2000000000000000^8463 ≤ 2000348182203289^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035977463328430139 50000000000000000000 2000348182203289 2000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000348182203289/2000000000000000 : ℝ)) (X := (50035977463328430139/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10867045431103223/100000000000000000000 : ℝ) ≤ ((7379719112137976069/7382000000000000000 : ℝ)+2*(607500574849/369100000000000 : ℝ)*(1373/12500 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (7379719112137976069/7382000000000000000 : ℝ)+2*(607500574849/369100000000000 : ℝ)*(1373/12500 : ℝ)=(10000525909866747/10000000000000000 : ℝ) by norm_num, show 1+2*(10867045431103223/100000000000000000000 : ℝ)=(50010867045431103223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35977463328430139/100000000000000000000 : ℝ)+(10867045431103223/100000000000000000000 : ℝ) ≤ ((7379719112137976069/7382000000000000000 : ℝ)+(607500574849/369100000000000 : ℝ)*((587/4000 : ℝ)+(1373/12500 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (7379719112137976069/7382000000000000000 : ℝ)+(607500574849/369100000000000 : ℝ)*((587/4000 : ℝ)+(1373/12500 : ℝ))=(2500283352610399/2500000000000000 : ℝ) by norm_num, show 1+(35977463328430139/100000000000000000000 : ℝ)+(10867045431103223/100000000000000000000 : ℝ)=(50023422254379766681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35977463328430139/100000000000000000000 : ℝ) ≤ ((7379719112137976069/7382000000000000000 : ℝ)+2*(607500574849/369100000000000 : ℝ)*(587/4000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (7379719112137976069/7382000000000000000 : ℝ)+2*(607500574849/369100000000000 : ℝ)*(587/4000 : ℝ)=(2000348182203289/2000000000000000 : ℝ) by norm_num, show 1+2*(35977463328430139/100000000000000000000 : ℝ)=(50035977463328430139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7379719112137976069/7382000000000000000 : ℝ)*(X 1 0+X 2 0)+(607500574849/369100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (587/4000 : ℝ)) (c := (7379719112137976069/7382000000000000000 : ℝ)) (alpha := (607500574849/369100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7379719112137976069/7382000000000000000 : ℝ)*(X 0 1+X 2 1)+(607500574849/369100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (587/4000 : ℝ)) (c := (7379719112137976069/7382000000000000000 : ℝ)) (alpha := (607500574849/369100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7379719112137976069/7382000000000000000 : ℝ)*(X 0 2+X 1 2)+(607500574849/369100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (587/4000 : ℝ)) (c := (7379719112137976069/7382000000000000000 : ℝ)) (alpha := (607500574849/369100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2106186859/10000000000 : ℝ)*X 0 0+(5396346557/10000000000 : ℝ)*X 0 1+(5262225319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5220306/9765625 : ℝ)*X 1 0+(-1087133349/5000000000 : ℝ)*X 1 1+(2631112631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345593557/10000000000 : ℝ)*X 2 0+(5262225127/10000000000 : ℝ)*X 2 1+(-2174266593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((543314949/1250000000 : ℝ)*X 0 0+(2105899603/5000000000 : ℝ)*X 0 1+(1121349529/2500000000 : ℝ)*X 0 2+(543314949/1250000000 : ℝ)*X 1 0+(2105899603/5000000000 : ℝ)*X 1 1+(1121349529/2500000000 : ℝ)*X 1 2+(543314949/1250000000 : ℝ)*X 2 0+(2105899603/5000000000 : ℝ)*X 2 1+(1121349529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-421238549/2000000000 : ℝ)*X 0 0+(1315648517/2500000000 : ℝ)*X 0 1+(674497049/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311307253/10000000000 : ℝ)*X 1 0+(-2040515353/10000000000 : ℝ)*X 1 1+(674497049/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311307349/10000000000 : ℝ)*X 2 0+(1348994067/2500000000 : ℝ)*X 2 1+(-1020257697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869306409/2000000000 : ℝ)*X 0 0+(2242322763/5000000000 : ℝ)*X 0 1+(263284653/625000000 : ℝ)*X 0 2+(869306409/2000000000 : ℝ)*X 1 0+(2242322763/5000000000 : ℝ)*X 1 1+(263284653/625000000 : ℝ)*X 1 2+(869306409/2000000000 : ℝ)*X 2 0+(2242322763/5000000000 : ℝ)*X 2 1+(263284653/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1895268861894114777316363023/184550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (384087097/25000000000000 : ℝ)*(base19) + (3390403/195312500000 : ℝ)*(base23) + (55575289/50000000000000 : ℝ)*(upper3) + (10429643/20000000000000 : ℝ)*(upper4) + (127773453/50000000000000 : ℝ)*(upper5) + (5555520128441889/100000000000000 : ℝ)*(major0) + (5555520128441889/100000000000000 : ℝ)*(major1) + (5555520128441889/100000000000000 : ℝ)*(major2) + (7455972195716771/100000000000000 : ℝ)*(sp0) + (7456013592660847/100000000000000 : ℝ)*(sp1) + (7456013393122899/100000000000000 : ℝ)*(sp2) + (228437838460341/6250000000000 : ℝ)*(sp3) + (2683330779/6250000000000 : ℝ)*(sp4) + (19370186513/100000000000000 : ℝ)*(sp7) + (114219524548499/3125000000000 : ℝ)*(f.failure) + (1491203025801847/20000000000000 : ℝ)*(f.sum) + (35742328640179/18455000000000000000000000000 : ℝ)*base66 + (20654559614494225659/738200000000000000000000000000000 : ℝ)*base68 + (1441904932243025659/738200000000000000000000000000000 : ℝ)*base70 + (8646109350036625659/738200000000000000000000000000000 : ℝ)*base72 + (60320854507679/18455000000000000000000000000 : ℝ)*base74 + (4835470921484425659/738200000000000000000000000000000 : ℝ)*base76 + (9047836439338374341/738200000000000000000000000000000 : ℝ)*base77 + (5911503953341025659/738200000000000000000000000000000 : ℝ)*base80 + (13842350574077/9227500000000000000000000000 : ℝ)*base82 + (387223/39062500000000000000 : ℝ)*base90 + (387223/39062500000000000000 : ℝ)*base92 + (387223/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1187395082262721247900254047/369100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184340269/25000000000000 : ℝ)*(base19) + (487905897/50000000000000 : ℝ)*(base23) + (31017271/100000000000000 : ℝ)*(upper3) + (15386187/25000000000000 : ℝ)*(lower4) + (6331169/5000000000000 : ℝ)*(upper5) + (5586243686096879/100000000000000 : ℝ)*(major0) + (5586243686096879/100000000000000 : ℝ)*(major1) + (5586243686096879/100000000000000 : ℝ)*(major2) + (5765661787/25000000000000 : ℝ)*(sp1) + (4211779549/20000000000000 : ℝ)*(sp2) + (479823947831/6400000000 : ℝ)*(sp4) + (7497225384851151/100000000000000 : ℝ)*(sp5) + (1499445430029967/20000000000000 : ℝ)*(sp6) + (367523808010101/10000000000000 : ℝ)*(sp7) + (367523808010101/10000000000000 : ℝ)*(f.failure) + (479823947831/6400000000 : ℝ)*(f.sum) + (28176823346427/9227500000000000000000000000 : ℝ)*base66 + (504626662611008651/738200000000000000000000000000000 : ℝ)*base67 + (7716410512492991349/738200000000000000000000000000000 : ℝ)*base70 + (813432106960008651/738200000000000000000000000000000 : ℝ)*base71 + (4568637891211/4613750000000000000000000000 : ℝ)*base74 + (10968904220129408651/738200000000000000000000000000000 : ℝ)*base75 + (2345610095662991349/738200000000000000000000000000000 : ℝ)*base78 + (4446780722008651/738200000000000000000000000000000 : ℝ)*base79 + (6466331297469/1153437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (94699/62500000000000000000 : ℝ)*base89 + (94699/62500000000000000000 : ℝ)*base91 + (94699/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1270_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (587/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1270_s5_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-526648619/2500000000 : ℝ)*x 0 + (2695859079/5000000000 : ℝ)*x 1 + (5266585519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526648619/2500000000 : ℝ)^529 ≤ (3203366552261/25000000000000 : ℝ)^401 := by
    have hnat : (526648619 : ℕ)^529*25000000000000^401 ≤ 3203366552261^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526648619 2500000000 3203366552261 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695859079/5000000000 : ℝ)^529 ≤ (1383387939733/3125000000000 : ℝ)^401 := by
    have hnat : (2695859079 : ℕ)^529*3125000000000^401 ≤ 1383387939733^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695859079 5000000000 1383387939733 3125000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266585519/10000000000 : ℝ)^529 ≤ (42918119712311/100000000000000 : ℝ)^401 := by
    have hnat : (5266585519 : ℕ)^529*100000000000000^401 ≤ 42918119712311^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266585519 10000000000 42918119712311 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526648619/2500000000 : ℝ), (2695859079/5000000000 : ℝ), (5266585519/10000000000 : ℝ)] ![(3203366552261/25000000000000 : ℝ), (1383387939733/3125000000000 : ℝ), (42918119712311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526648619/2500000000 : ℝ)|^529 ≤ (3203366552261/25000000000000 : ℝ)^401
        have hw : |(-526648619/2500000000 : ℝ)|=(526648619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695859079/5000000000 : ℝ)|^529 ≤ (1383387939733/3125000000000 : ℝ)^401
        have hw : |(2695859079/5000000000 : ℝ)|=(2695859079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266585519/10000000000 : ℝ)|^529 ≤ (42918119712311/100000000000000 : ℝ)^401
        have hw : |(5266585519/10000000000 : ℝ)|=(5266585519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344420091/10000000000 : ℝ)*x 0 + (-1085023109/5000000000 : ℝ)*x 1 + (5266585793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344420091/10000000000 : ℝ)^529 ≤ (10939209039973/25000000000000 : ℝ)^401 := by
    have hnat : (5344420091 : ℕ)^529*25000000000000^401 ≤ 10939209039973^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344420091 10000000000 10939209039973 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085023109/5000000000 : ℝ)^529 ≤ (13325041167351/100000000000000 : ℝ)^401 := by
    have hnat : (1085023109 : ℕ)^529*100000000000000^401 ≤ 13325041167351^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085023109 5000000000 13325041167351 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266585793/10000000000 : ℝ)^529 ≤ (42918122657909/100000000000000 : ℝ)^401 := by
    have hnat : (5266585793 : ℕ)^529*100000000000000^401 ≤ 42918122657909^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266585793 10000000000 42918122657909 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344420091/10000000000 : ℝ), (-1085023109/5000000000 : ℝ), (5266585793/10000000000 : ℝ)] ![(10939209039973/25000000000000 : ℝ), (13325041167351/100000000000000 : ℝ), (42918122657909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344420091/10000000000 : ℝ)|^529 ≤ (10939209039973/25000000000000 : ℝ)^401
        have hw : |(5344420091/10000000000 : ℝ)|=(5344420091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085023109/5000000000 : ℝ)|^529 ≤ (13325041167351/100000000000000 : ℝ)^401
        have hw : |(-1085023109/5000000000 : ℝ)|=(1085023109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266585793/10000000000 : ℝ)|^529 ≤ (42918122657909/100000000000000 : ℝ)^401
        have hw : |(5266585793/10000000000 : ℝ)|=(5266585793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344419073/10000000000 : ℝ)*x 0 + (5266586737/10000000000 : ℝ)*x 1 + (-1085023161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344419073/10000000000 : ℝ)^529 ≤ (2187841258233/5000000000000 : ℝ)^401 := by
    have hnat : (5344419073 : ℕ)^529*5000000000000^401 ≤ 2187841258233^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344419073 10000000000 2187841258233 5000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266586737/10000000000 : ℝ)^529 ≤ (8583626561249/20000000000000 : ℝ)^401 := by
    have hnat : (5266586737 : ℕ)^529*20000000000000^401 ≤ 8583626561249^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266586737 10000000000 8583626561249 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085023161/5000000000 : ℝ)^529 ≤ (13325042009801/100000000000000 : ℝ)^401 := by
    have hnat : (1085023161 : ℕ)^529*100000000000000^401 ≤ 13325042009801^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085023161 5000000000 13325042009801 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344419073/10000000000 : ℝ), (5266586737/10000000000 : ℝ), (-1085023161/5000000000 : ℝ)] ![(2187841258233/5000000000000 : ℝ), (8583626561249/20000000000000 : ℝ), (13325042009801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344419073/10000000000 : ℝ)|^529 ≤ (2187841258233/5000000000000 : ℝ)^401
        have hw : |(5344419073/10000000000 : ℝ)|=(5344419073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266586737/10000000000 : ℝ)|^529 ≤ (8583626561249/20000000000000 : ℝ)^401
        have hw : |(5266586737/10000000000 : ℝ)|=(5266586737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1085023161/5000000000 : ℝ)|^529 ≤ (13325042009801/100000000000000 : ℝ)^401
        have hw : |(-1085023161/5000000000 : ℝ)|=(1085023161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (869351731/2000000000 : ℝ)*x 0 + (4220938129/10000000000 : ℝ)*x 1 + (447619817/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869351731/2000000000 : ℝ)^529 ≤ (8329275953393/25000000000000 : ℝ)^401 := by
    have hnat : (869351731 : ℕ)^529*25000000000000^401 ≤ 8329275953393^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869351731 2000000000 8329275953393 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4220938129/10000000000 : ℝ)^529 ≤ (16025396797831/50000000000000 : ℝ)^401 := by
    have hnat : (4220938129 : ℕ)^529*50000000000000^401 ≤ 16025396797831^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220938129 10000000000 16025396797831 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447619817/1000000000 : ℝ)^529 ≤ (34632102578813/100000000000000 : ℝ)^401 := by
    have hnat : (447619817 : ℕ)^529*100000000000000^401 ≤ 34632102578813^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447619817 1000000000 34632102578813 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869351731/2000000000 : ℝ), (4220938129/10000000000 : ℝ), (447619817/1000000000 : ℝ)] ![(8329275953393/25000000000000 : ℝ), (16025396797831/50000000000000 : ℝ), (34632102578813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869351731/2000000000 : ℝ)|^529 ≤ (8329275953393/25000000000000 : ℝ)^401
        have hw : |(869351731/2000000000 : ℝ)|=(869351731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4220938129/10000000000 : ℝ)|^529 ≤ (16025396797831/50000000000000 : ℝ)^401
        have hw : |(4220938129/10000000000 : ℝ)|=(4220938129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447619817/1000000000 : ℝ)|^529 ≤ (34632102578813/100000000000000 : ℝ)^401
        have hw : |(447619817/1000000000 : ℝ)|=(447619817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-131662409/625000000 : ℝ)*x 0 + (1316726887/2500000000 : ℝ)*x 1 + (2695697757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131662409/625000000 : ℝ)^529 ≤ (6406749425571/50000000000000 : ℝ)^401 := by
    have hnat : (131662409 : ℕ)^529*50000000000000^401 ≤ 6406749425571^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131662409 625000000 6406749425571 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316726887/2500000000 : ℝ)^529 ≤ (21460790836241/50000000000000 : ℝ)^401 := by
    have hnat : (1316726887 : ℕ)^529*50000000000000^401 ≤ 21460790836241^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316726887 2500000000 21460790836241 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695697757/5000000000 : ℝ)^529 ≤ (1770596778841/4000000000000 : ℝ)^401 := by
    have hnat : (2695697757 : ℕ)^529*4000000000000^401 ≤ 1770596778841^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695697757 5000000000 1770596778841 4000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131662409/625000000 : ℝ), (1316726887/2500000000 : ℝ), (2695697757/5000000000 : ℝ)] ![(6406749425571/50000000000000 : ℝ), (21460790836241/50000000000000 : ℝ), (1770596778841/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131662409/625000000 : ℝ)|^529 ≤ (6406749425571/50000000000000 : ℝ)^401
        have hw : |(-131662409/625000000 : ℝ)|=(131662409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316726887/2500000000 : ℝ)|^529 ≤ (21460790836241/50000000000000 : ℝ)^401
        have hw : |(1316726887/2500000000 : ℝ)|=(1316726887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695697757/5000000000 : ℝ)|^529 ≤ (1770596778841/4000000000000 : ℝ)^401
        have hw : |(2695697757/5000000000 : ℝ)|=(2695697757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (332026867/625000000 : ℝ)*x 0 + (-511309359/2500000000 : ℝ)*x 1 + (2695697753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332026867/625000000 : ℝ)^529 ≤ (21705823090163/50000000000000 : ℝ)^401 := by
    have hnat : (332026867 : ℕ)^529*50000000000000^401 ≤ 21705823090163^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332026867 625000000 21705823090163 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511309359/2500000000 : ℝ)^529 ≤ (6161717207033/50000000000000 : ℝ)^401 := by
    have hnat : (511309359 : ℕ)^529*50000000000000^401 ≤ 6161717207033^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511309359 2500000000 6161717207033 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695697753/5000000000 : ℝ)^529 ≤ (44264919384377/100000000000000 : ℝ)^401 := by
    have hnat : (2695697753 : ℕ)^529*100000000000000^401 ≤ 44264919384377^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695697753 5000000000 44264919384377 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332026867/625000000 : ℝ), (-511309359/2500000000 : ℝ), (2695697753/5000000000 : ℝ)] ![(21705823090163/50000000000000 : ℝ), (6161717207033/50000000000000 : ℝ), (44264919384377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332026867/625000000 : ℝ)|^529 ≤ (21705823090163/50000000000000 : ℝ)^401
        have hw : |(332026867/625000000 : ℝ)|=(332026867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511309359/2500000000 : ℝ)|^529 ≤ (6161717207033/50000000000000 : ℝ)^401
        have hw : |(-511309359/2500000000 : ℝ)|=(511309359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695697753/5000000000 : ℝ)|^529 ≤ (44264919384377/100000000000000 : ℝ)^401
        have hw : |(2695697753/5000000000 : ℝ)|=(2695697753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1328107471/2500000000 : ℝ)*x 0 + (5391395499/10000000000 : ℝ)*x 1 + (-204523743/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328107471/2500000000 : ℝ)^529 ≤ (5426455788711/12500000000000 : ℝ)^401 := by
    have hnat : (1328107471 : ℕ)^529*12500000000000^401 ≤ 5426455788711^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328107471 2500000000 5426455788711 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391395499/10000000000 : ℝ)^529 ≤ (553311491357/1250000000000 : ℝ)^401 := by
    have hnat : (5391395499 : ℕ)^529*1250000000000^401 ≤ 553311491357^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391395499 10000000000 553311491357 1250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204523743/1000000000 : ℝ)^529 ≤ (6161717183187/50000000000000 : ℝ)^401 := by
    have hnat : (204523743 : ℕ)^529*50000000000000^401 ≤ 6161717183187^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204523743 1000000000 6161717183187 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328107471/2500000000 : ℝ), (5391395499/10000000000 : ℝ), (-204523743/1000000000 : ℝ)] ![(5426455788711/12500000000000 : ℝ), (553311491357/1250000000000 : ℝ), (6161717183187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328107471/2500000000 : ℝ)|^529 ≤ (5426455788711/12500000000000 : ℝ)^401
        have hw : |(1328107471/2500000000 : ℝ)|=(1328107471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391395499/10000000000 : ℝ)|^529 ≤ (553311491357/1250000000000 : ℝ)^401
        have hw : |(5391395499/10000000000 : ℝ)|=(5391395499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204523743/1000000000 : ℝ)|^529 ≤ (6161717183187/50000000000000 : ℝ)^401
        have hw : |(-204523743/1000000000 : ℝ)|=(204523743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s5_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346768429/10000000000 : ℝ)*x 0 + (447554311/1000000000 : ℝ)*x 1 + (1055398921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346768429/10000000000 : ℝ)^529 ≤ (33317202642823/100000000000000 : ℝ)^401 := by
    have hnat : (4346768429 : ℕ)^529*100000000000000^401 ≤ 33317202642823^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346768429 10000000000 33317202642823 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447554311/1000000000 : ℝ)^529 ≤ (4328177100413/12500000000000 : ℝ)^401 := by
    have hnat : (447554311 : ℕ)^529*12500000000000^401 ≤ 4328177100413^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447554311 1000000000 4328177100413 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055398921/2500000000 : ℝ)^529 ≤ (4007172567479/12500000000000 : ℝ)^401 := by
    have hnat : (1055398921 : ℕ)^529*12500000000000^401 ≤ 4007172567479^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055398921 2500000000 4007172567479 12500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346768429/10000000000 : ℝ), (447554311/1000000000 : ℝ), (1055398921/2500000000 : ℝ)] ![(33317202642823/100000000000000 : ℝ), (4328177100413/12500000000000 : ℝ), (4007172567479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346768429/10000000000 : ℝ)|^529 ≤ (33317202642823/100000000000000 : ℝ)^401
        have hw : |(4346768429/10000000000 : ℝ)|=(4346768429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447554311/1000000000 : ℝ)|^529 ≤ (4328177100413/12500000000000 : ℝ)^401
        have hw : |(447554311/1000000000 : ℝ)|=(447554311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055398921/2500000000 : ℝ)|^529 ≤ (4007172567479/12500000000000 : ℝ)^401
        have hw : |(1055398921/2500000000 : ℝ)|=(1055398921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11491/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7071/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5699/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5699/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5699/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5699/50000 : ℝ) ^ (8463/2048 : ℝ) ≤ (12662230028295063/100000000000000000000 : ℝ) := by
    have hpowers : (5699/50000 : ℝ)^8463 ≤ (12662230028295063/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5699 : ℕ)^8463*100000000000000000000^2048 ≤ 12662230028295063^2048*50000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5699 50000 12662230028295063 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5699/50000 : ℝ)) (X := (12662230028295063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (31761630930473943/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8463 ≤ (31761630930473943/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8463*100000000000000000000^2048 ≤ 31761630930473943^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 31761630930473943 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (31761630930473943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012662230028295063/50000000000000000000 : ℝ) ≤ (1000061277935673/1000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50012662230028295063/50000000000000000000 : ℝ)^2048 ≤ (1000061277935673/1000000000000000 : ℝ)^8463 := by
      have hnat : (50012662230028295063 : ℕ)^2048*1000000000000000^8463 ≤ 1000061277935673^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012662230028295063 50000000000000000000 1000061277935673 1000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000061277935673/1000000000000000 : ℝ)) (X := (50012662230028295063/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022211930479384503/50000000000000000000 : ℝ) ≤ (5000537426167617/5000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50022211930479384503/50000000000000000000 : ℝ)^2048 ≤ (5000537426167617/5000000000000000 : ℝ)^8463 := by
      have hnat : (50022211930479384503 : ℕ)^2048*5000000000000000^8463 ≤ 5000537426167617^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022211930479384503 50000000000000000000 5000537426167617 5000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000537426167617/5000000000000000 : ℝ)) (X := (50022211930479384503/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031761630930473943/50000000000000000000 : ℝ) ≤ (5000768462656869/5000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50031761630930473943/50000000000000000000 : ℝ)^2048 ≤ (5000768462656869/5000000000000000 : ℝ)^8463 := by
      have hnat : (50031761630930473943 : ℕ)^2048*5000000000000000^8463 ≤ 5000768462656869^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031761630930473943 50000000000000000000 5000768462656869 5000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000768462656869/5000000000000000 : ℝ)) (X := (50031761630930473943/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12662230028295063/100000000000000000000 : ℝ) ≤ ((4733534581755748791/4735000000000000000 : ℝ)+2*(19253040771/11837500000000 : ℝ)*(5699/50000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (4733534581755748791/4735000000000000000 : ℝ)+2*(19253040771/11837500000000 : ℝ)*(5699/50000 : ℝ)=(1000061277935673/1000000000000000 : ℝ) by norm_num, show 1+2*(12662230028295063/100000000000000000000 : ℝ)=(50012662230028295063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31761630930473943/100000000000000000000 : ℝ)+(12662230028295063/100000000000000000000 : ℝ) ≤ ((4733534581755748791/4735000000000000000 : ℝ)+(19253040771/11837500000000 : ℝ)*((14239/100000 : ℝ)+(5699/50000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (4733534581755748791/4735000000000000000 : ℝ)+(19253040771/11837500000000 : ℝ)*((14239/100000 : ℝ)+(5699/50000 : ℝ))=(5000537426167617/5000000000000000 : ℝ) by norm_num, show 1+(31761630930473943/100000000000000000000 : ℝ)+(12662230028295063/100000000000000000000 : ℝ)=(50022211930479384503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31761630930473943/100000000000000000000 : ℝ) ≤ ((4733534581755748791/4735000000000000000 : ℝ)+2*(19253040771/11837500000000 : ℝ)*(14239/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (4733534581755748791/4735000000000000000 : ℝ)+2*(19253040771/11837500000000 : ℝ)*(14239/100000 : ℝ)=(5000768462656869/5000000000000000 : ℝ) by norm_num, show 1+2*(31761630930473943/100000000000000000000 : ℝ)=(50031761630930473943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4733534581755748791/4735000000000000000 : ℝ)*(X 1 0+X 2 0)+(19253040771/11837500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (4733534581755748791/4735000000000000000 : ℝ)) (alpha := (19253040771/11837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4733534581755748791/4735000000000000000 : ℝ)*(X 0 1+X 2 1)+(19253040771/11837500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (4733534581755748791/4735000000000000000 : ℝ)) (alpha := (19253040771/11837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4733534581755748791/4735000000000000000 : ℝ)*(X 0 2+X 1 2)+(19253040771/11837500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (5699/50000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (4733534581755748791/4735000000000000000 : ℝ)) (alpha := (19253040771/11837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526648619/2500000000 : ℝ)*X 0 0+(2695859079/5000000000 : ℝ)*X 0 1+(5266585519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344420091/10000000000 : ℝ)*X 1 0+(-1085023109/5000000000 : ℝ)*X 1 1+(5266585793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344419073/10000000000 : ℝ)*X 2 0+(5266586737/10000000000 : ℝ)*X 2 1+(-1085023161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869351731/2000000000 : ℝ)*X 0 0+(4220938129/10000000000 : ℝ)*X 0 1+(447619817/1000000000 : ℝ)*X 0 2+(869351731/2000000000 : ℝ)*X 1 0+(4220938129/10000000000 : ℝ)*X 1 1+(447619817/1000000000 : ℝ)*X 1 2+(869351731/2000000000 : ℝ)*X 2 0+(4220938129/10000000000 : ℝ)*X 2 1+(447619817/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-131662409/625000000 : ℝ)*X 0 0+(1316726887/2500000000 : ℝ)*X 0 1+(2695697757/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332026867/625000000 : ℝ)*X 1 0+(-511309359/2500000000 : ℝ)*X 1 1+(2695697753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328107471/2500000000 : ℝ)*X 2 0+(5391395499/10000000000 : ℝ)*X 2 1+(-204523743/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346768429/10000000000 : ℝ)*X 0 0+(447554311/1000000000 : ℝ)*X 0 1+(1055398921/2500000000 : ℝ)*X 0 2+(4346768429/10000000000 : ℝ)*X 1 0+(447554311/1000000000 : ℝ)*X 1 1+(1055398921/2500000000 : ℝ)*X 1 2+(4346768429/10000000000 : ℝ)*X 2 0+(447554311/1000000000 : ℝ)*X 2 1+(1055398921/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11514653390369087434011/4735000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860671299/20000000000000 : ℝ)*(base19) + (2345205601/100000000000000 : ℝ)*(base23) + (16035257/10000000000000 : ℝ)*(upper2) + (188698847/25000000000000 : ℝ)*(upper3) + (393305001/100000000000000 : ℝ)*(upper4) + (2977370612685399/50000000000000 : ℝ)*(major0) + (2977370612685399/50000000000000 : ℝ)*(major1) + (2977370612685399/50000000000000 : ℝ)*(major2) + (1598337258940123/20000000000000 : ℝ)*(sp0) + (7991802265124153/100000000000000 : ℝ)*(sp1) + (7991804223275047/100000000000000 : ℝ)*(sp2) + (3917619727459787/100000000000000 : ℝ)*(sp3) + (120273780033/100000000000000 : ℝ)*(sp4) + (7009217573/12500000000000 : ℝ)*(sp7) + (3917675801200371/100000000000000 : ℝ)*(f.failure) + (998975821060081/12500000000000 : ℝ)*(f.sum) + (1021907805751/4735000000000000000000000000 : ℝ)*base66 + (139554603665547391/236750000000000000000000000000000 : ℝ)*base68 + (1565295315316452609/236750000000000000000000000000000 : ℝ)*base69 + (800782184382797391/236750000000000000000000000000000 : ℝ)*base72 + (1712919879551/4735000000000000000000000000 : ℝ)*base74 + (42379116227952609/236750000000000000000000000000000 : ℝ)*base75 + (6346886517598202609/236750000000000000000000000000000 : ℝ)*base77 + (7683497561064297391/236750000000000000000000000000000 : ℝ)*base80 + (1746051316141/295937500000000000000000000 : ℝ)*base82 + (4274571/625000000000000000000 : ℝ)*base90 + (4274571/625000000000000000000 : ℝ)*base92 + (4274571/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133895100017981840880255681/29593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (776704759/100000000000000 : ℝ)*(base19) + (882510901/100000000000000 : ℝ)*(base23) + (84687567/100000000000000 : ℝ)*(upper3) + (19569019/50000000000000 : ℝ)*(lower4) + (93006821/100000000000000 : ℝ)*(upper5) + (748170447540801/12500000000000 : ℝ)*(major0) + (748170447540801/12500000000000 : ℝ)*(major1) + (748170447540801/12500000000000 : ℝ)*(major2) + (21379635217/100000000000000 : ℝ)*(sp1) + (5925843413/25000000000000 : ℝ)*(sp2) + (8032904496220789/100000000000000 : ℝ)*(sp4) + (8032882339880813/100000000000000 : ℝ)*(sp5) + (2008219977584059/25000000000000 : ℝ)*(sp6) + (1968911256808699/50000000000000 : ℝ)*(sp7) + (1968911256808699/50000000000000 : ℝ)*(f.failure) + (8032904496220789/100000000000000 : ℝ)*(f.sum) + (7892568146967/2367500000000000000000000000 : ℝ)*base65 + (966552183998321591/59187500000000000000000000000000 : ℝ)*base67 + (819743057634446591/59187500000000000000000000000000 : ℝ)*base69 + (558396647527634091/59187500000000000000000000000000 : ℝ)*base71 + (15475063430567/2367500000000000000000000000 : ℝ)*base73 + (737451248658759091/59187500000000000000000000000000 : ℝ)*base75 + (503816862618946591/59187500000000000000000000000000 : ℝ)*base77 + (1376908596470071591/59187500000000000000000000000000 : ℝ)*base79 + (933991667333/591875000000000000000000000 : ℝ)*base81 + (3048499/312500000000000000000 : ℝ)*base90 + (3048499/312500000000000000000 : ℝ)*base92 + (3048499/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1270_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5699/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1270_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1270_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1270_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1270_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16149/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1923/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1270_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
