-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:09.2225+00:00
-- url     : https://prove2.me/submissions/828eb891-672b-4eec-8933-da0ef51e8613

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
theorem support_rectangle_w1138_s6_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-17350167/80000000 : ℝ)*x 0 + (539346153/1000000000 : ℝ)*x 1 + (5265338459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17350167/80000000 : ℝ)^8331 ≤ (3294477875999/25000000000000 : ℝ)^6283 := by
    have hnat : (17350167 : ℕ)^8331*25000000000000^6283 ≤ 3294477875999^6283*80000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17350167 80000000 3294477875999 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539346153/1000000000 : ℝ)^8331 ≤ (44102928537033/100000000000000 : ℝ)^6283 := by
    have hnat : (539346153 : ℕ)^8331*100000000000000^6283 ≤ 44102928537033^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539346153 1000000000 44102928537033 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265338459/10000000000 : ℝ)^8331 ≤ (21359579968609/50000000000000 : ℝ)^6283 := by
    have hnat : (5265338459 : ℕ)^8331*50000000000000^6283 ≤ 21359579968609^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265338459 10000000000 21359579968609 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17350167/80000000 : ℝ), (539346153/1000000000 : ℝ), (5265338459/10000000000 : ℝ)] ![(3294477875999/25000000000000 : ℝ), (44102928537033/100000000000000 : ℝ), (21359579968609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17350167/80000000 : ℝ)|^8331 ≤ (3294477875999/25000000000000 : ℝ)^6283
        have hw : |(-17350167/80000000 : ℝ)|=(17350167/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539346153/1000000000 : ℝ)|^8331 ≤ (44102928537033/100000000000000 : ℝ)^6283
        have hw : |(539346153/1000000000 : ℝ)|=(539346153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265338459/10000000000 : ℝ)|^8331 ≤ (21359579968609/50000000000000 : ℝ)^6283
        have hw : |(5265338459/10000000000 : ℝ)|=(5265338459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344861579/10000000000 : ℝ)*x 0 + (-2233763107/10000000000 : ℝ)*x 1 + (131633461/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344861579/10000000000 : ℝ)^8331 ≤ (43576758417947/100000000000000 : ℝ)^6283 := by
    have hnat : (5344861579 : ℕ)^8331*100000000000000^6283 ≤ 43576758417947^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344861579 10000000000 43576758417947 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233763107/10000000000 : ℝ)^8331 ≤ (1370408183967/10000000000000 : ℝ)^6283 := by
    have hnat : (2233763107 : ℕ)^8331*10000000000000^6283 ≤ 1370408183967^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233763107 10000000000 1370408183967 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131633461/250000000 : ℝ)^8331 ≤ (42719159732819/100000000000000 : ℝ)^6283 := by
    have hnat : (131633461 : ℕ)^8331*100000000000000^6283 ≤ 42719159732819^6283*250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131633461 250000000 42719159732819 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344861579/10000000000 : ℝ), (-2233763107/10000000000 : ℝ), (131633461/250000000 : ℝ)] ![(43576758417947/100000000000000 : ℝ), (1370408183967/10000000000000 : ℝ), (42719159732819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344861579/10000000000 : ℝ)|^8331 ≤ (43576758417947/100000000000000 : ℝ)^6283
        have hw : |(5344861579/10000000000 : ℝ)|=(5344861579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233763107/10000000000 : ℝ)|^8331 ≤ (1370408183967/10000000000000 : ℝ)^6283
        have hw : |(-2233763107/10000000000 : ℝ)|=(2233763107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131633461/250000000 : ℝ)|^8331 ≤ (42719159732819/100000000000000 : ℝ)^6283
        have hw : |(131633461/250000000 : ℝ)|=(131633461/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672430779/5000000000 : ℝ)*x 0 + (5265338449/10000000000 : ℝ)*x 1 + (-1116881561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672430779/5000000000 : ℝ)^8331 ≤ (1743070327637/4000000000000 : ℝ)^6283 := by
    have hnat : (2672430779 : ℕ)^8331*4000000000000^6283 ≤ 1743070327637^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672430779 5000000000 1743070327637 4000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265338449/10000000000 : ℝ)^8331 ≤ (1067978995741/2500000000000 : ℝ)^6283 := by
    have hnat : (5265338449 : ℕ)^8331*2500000000000^6283 ≤ 1067978995741^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265338449 10000000000 1067978995741 2500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116881561/5000000000 : ℝ)^8331 ≤ (13704081961691/100000000000000 : ℝ)^6283 := by
    have hnat : (1116881561 : ℕ)^8331*100000000000000^6283 ≤ 13704081961691^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116881561 5000000000 13704081961691 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672430779/5000000000 : ℝ), (5265338449/10000000000 : ℝ), (-1116881561/5000000000 : ℝ)] ![(1743070327637/4000000000000 : ℝ), (1067978995741/2500000000000 : ℝ), (13704081961691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672430779/5000000000 : ℝ)|^8331 ≤ (1743070327637/4000000000000 : ℝ)^6283
        have hw : |(2672430779/5000000000 : ℝ)|=(2672430779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265338449/10000000000 : ℝ)|^8331 ≤ (1067978995741/2500000000000 : ℝ)^6283
        have hw : |(5265338449/10000000000 : ℝ)|=(5265338449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1116881561/5000000000 : ℝ)|^8331 ≤ (13704081961691/100000000000000 : ℝ)^6283
        have hw : |(-1116881561/5000000000 : ℝ)|=(1116881561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365219291/10000000000 : ℝ)*x 0 + (423972069/1000000000 : ℝ)*x 1 + (2247209181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365219291/10000000000 : ℝ)^8331 ≤ (33316765015001/100000000000000 : ℝ)^6283 := by
    have hnat : (4365219291 : ℕ)^8331*100000000000000^6283 ≤ 33316765015001^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365219291 10000000000 33316765015001 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423972069/1000000000 : ℝ)^8331 ≤ (32052690614817/100000000000000 : ℝ)^6283 := by
    have hnat : (423972069 : ℕ)^8331*100000000000000^6283 ≤ 32052690614817^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423972069 1000000000 32052690614817 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247209181/5000000000 : ℝ)^8331 ≤ (17315272178159/50000000000000 : ℝ)^6283 := by
    have hnat : (2247209181 : ℕ)^8331*50000000000000^6283 ≤ 17315272178159^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247209181 5000000000 17315272178159 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365219291/10000000000 : ℝ), (423972069/1000000000 : ℝ), (2247209181/5000000000 : ℝ)] ![(33316765015001/100000000000000 : ℝ), (32052690614817/100000000000000 : ℝ), (17315272178159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365219291/10000000000 : ℝ)|^8331 ≤ (33316765015001/100000000000000 : ℝ)^6283
        have hw : |(4365219291/10000000000 : ℝ)|=(4365219291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423972069/1000000000 : ℝ)|^8331 ≤ (32052690614817/100000000000000 : ℝ)^6283
        have hw : |(423972069/1000000000 : ℝ)|=(423972069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247209181/5000000000 : ℝ)|^8331 ≤ (17315272178159/50000000000000 : ℝ)^6283
        have hw : |(2247209181/5000000000 : ℝ)|=(2247209181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1084387977/5000000000 : ℝ)*x 0 + (5265661899/10000000000 : ℝ)*x 1 + (1078627367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084387977/5000000000 : ℝ)^8331 ≤ (13177952424537/100000000000000 : ℝ)^6283 := by
    have hnat : (1084387977 : ℕ)^8331*100000000000000^6283 ≤ 13177952424537^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084387977 5000000000 13177952424537 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265661899/10000000000 : ℝ)^8331 ≤ (42722639499077/100000000000000 : ℝ)^6283 := by
    have hnat : (5265661899 : ℕ)^8331*100000000000000^6283 ≤ 42722639499077^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265661899 10000000000 42722639499077 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078627367/2000000000 : ℝ)^8331 ≤ (44099408062089/100000000000000 : ℝ)^6283 := by
    have hnat : (1078627367 : ℕ)^8331*100000000000000^6283 ≤ 44099408062089^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078627367 2000000000 44099408062089 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1084387977/5000000000 : ℝ), (5265661899/10000000000 : ℝ), (1078627367/2000000000 : ℝ)] ![(13177952424537/100000000000000 : ℝ), (42722639499077/100000000000000 : ℝ), (44099408062089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1084387977/5000000000 : ℝ)|^8331 ≤ (13177952424537/100000000000000 : ℝ)^6283
        have hw : |(-1084387977/5000000000 : ℝ)|=(1084387977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265661899/10000000000 : ℝ)|^8331 ≤ (42722639499077/100000000000000 : ℝ)^6283
        have hw : |(5265661899/10000000000 : ℝ)|=(5265661899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078627367/2000000000 : ℝ)|^8331 ≤ (44099408062089/100000000000000 : ℝ)^6283
        have hw : |(1078627367/2000000000 : ℝ)|=(1078627367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656205347/5000000000 : ℝ)*x 0 + (-2105964831/10000000000 : ℝ)*x 1 + (5393136753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656205347/5000000000 : ℝ)^8331 ≤ (5403286689/12500000000 : ℝ)^6283 := by
    have hnat : (2656205347 : ℕ)^8331*12500000000^6283 ≤ 5403286689^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656205347 5000000000 5403286689 12500000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105964831/10000000000 : ℝ)^8331 ≤ (12674299305471/100000000000000 : ℝ)^6283 := by
    have hnat : (2105964831 : ℕ)^8331*100000000000000^6283 ≤ 12674299305471^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105964831 10000000000 12674299305471 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393136753/10000000000 : ℝ)^8331 ≤ (2204970358651/5000000000000 : ℝ)^6283 := by
    have hnat : (5393136753 : ℕ)^8331*5000000000000^6283 ≤ 2204970358651^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393136753 10000000000 2204970358651 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656205347/5000000000 : ℝ), (-2105964831/10000000000 : ℝ), (5393136753/10000000000 : ℝ)] ![(5403286689/12500000000 : ℝ), (12674299305471/100000000000000 : ℝ), (2204970358651/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656205347/5000000000 : ℝ)|^8331 ≤ (5403286689/12500000000 : ℝ)^6283
        have hw : |(2656205347/5000000000 : ℝ)|=(2656205347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105964831/10000000000 : ℝ)|^8331 ≤ (12674299305471/100000000000000 : ℝ)^6283
        have hw : |(-2105964831/10000000000 : ℝ)|=(2105964831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393136753/10000000000 : ℝ)|^8331 ≤ (2204970358651/5000000000000 : ℝ)^6283
        have hw : |(5393136753/10000000000 : ℝ)|=(5393136753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656205399/5000000000 : ℝ)*x 0 + (5393136561/10000000000 : ℝ)*x 1 + (-2105964951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656205399/5000000000 : ℝ)^8331 ≤ (4322629463407/10000000000000 : ℝ)^6283 := by
    have hnat : (2656205399 : ℕ)^8331*10000000000000^6283 ≤ 4322629463407^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656205399 5000000000 4322629463407 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393136561/10000000000 : ℝ)^8331 ≤ (44099405091299/100000000000000 : ℝ)^6283 := by
    have hnat : (5393136561 : ℕ)^8331*100000000000000^6283 ≤ 44099405091299^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393136561 10000000000 44099405091299 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105964951/10000000000 : ℝ)^8331 ≤ (12674300263071/100000000000000 : ℝ)^6283 := by
    have hnat : (2105964951 : ℕ)^8331*100000000000000^6283 ≤ 12674300263071^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105964951 10000000000 12674300263071 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656205399/5000000000 : ℝ), (5393136561/10000000000 : ℝ), (-2105964951/10000000000 : ℝ)] ![(4322629463407/10000000000000 : ℝ), (44099405091299/100000000000000 : ℝ), (12674300263071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656205399/5000000000 : ℝ)|^8331 ≤ (4322629463407/10000000000000 : ℝ)^6283
        have hw : |(2656205399/5000000000 : ℝ)|=(2656205399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393136561/10000000000 : ℝ)|^8331 ≤ (44099405091299/100000000000000 : ℝ)^6283
        have hw : |(5393136561/10000000000 : ℝ)|=(5393136561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105964951/10000000000 : ℝ)|^8331 ≤ (12674300263071/100000000000000 : ℝ)^6283
        have hw : |(-2105964951/10000000000 : ℝ)|=(2105964951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s6_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873045811/2000000000 : ℝ)*x 0 + (179751007/400000000 : ℝ)*x 1 + (16563931/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873045811/2000000000 : ℝ)^8331 ≤ (8329215957039/25000000000000 : ℝ)^6283 := by
    have hnat : (873045811 : ℕ)^8331*25000000000000^6283 ≤ 8329215957039^6283*2000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873045811 2000000000 8329215957039 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179751007/400000000 : ℝ)^8331 ≤ (17311986590721/50000000000000 : ℝ)^6283 := by
    have hnat : (179751007 : ℕ)^8331*50000000000000^6283 ≤ 17311986590721^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179751007 400000000 17311986590721 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16563931/39062500 : ℝ)^8331 ≤ (32059162973293/100000000000000 : ℝ)^6283 := by
    have hnat : (16563931 : ℕ)^8331*100000000000000^6283 ≤ 32059162973293^6283*39062500^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16563931 39062500 32059162973293 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873045811/2000000000 : ℝ), (179751007/400000000 : ℝ), (16563931/39062500 : ℝ)] ![(8329215957039/25000000000000 : ℝ), (17311986590721/50000000000000 : ℝ), (32059162973293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873045811/2000000000 : ℝ)|^8331 ≤ (8329215957039/25000000000000 : ℝ)^6283
        have hw : |(873045811/2000000000 : ℝ)|=(873045811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179751007/400000000 : ℝ)|^8331 ≤ (17311986590721/50000000000000 : ℝ)^6283
        have hw : |(179751007/400000000 : ℝ)|=(179751007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16563931/39062500 : ℝ)|^8331 ≤ (32059162973293/100000000000000 : ℝ)^6283
        have hw : |(16563931/39062500 : ℝ)|=(16563931/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11341/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2811/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (7061287290325911/50000000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^4165 ≤ (7061287290325911/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11309 : ℕ)^4165*50000000000000000000^1024 ≤ 7061287290325911^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 7061287290325911 50000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (7061287290325911/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (34507941726491181/100000000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^4165 ≤ (34507941726491181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14087 : ℕ)^4165*100000000000000000000^1024 ≤ 34507941726491181^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 34507941726491181 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (34507941726491181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007061287290325911/25000000000000000000 : ℝ) ≤ (10000694356610441/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (25007061287290325911/25000000000000000000 : ℝ)^1024 ≤ (10000694356610441/10000000000000000 : ℝ)^4165 := by
      have hnat : (25007061287290325911 : ℕ)^1024*10000000000000000^4165 ≤ 10000694356610441^4165*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007061287290325911 25000000000000000000 10000694356610441 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000694356610441/10000000000000000 : ℝ)) (X := (25007061287290325911/25000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048630516307143003/100000000000000000000 : ℝ) ≤ (5000597701318429/5000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (100048630516307143003/100000000000000000000 : ℝ)^1024 ≤ (5000597701318429/5000000000000000 : ℝ)^4165 := by
      have hnat : (100048630516307143003 : ℕ)^1024*5000000000000000^4165 ≤ 5000597701318429^4165*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048630516307143003 100000000000000000000 5000597701318429 5000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000597701318429/5000000000000000 : ℝ)) (X := (100048630516307143003/100000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034507941726491181/50000000000000000000 : ℝ) ≤ (400067857946531/400000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50034507941726491181/50000000000000000000 : ℝ)^1024 ≤ (400067857946531/400000000000000 : ℝ)^4165 := by
      have hnat : (50034507941726491181 : ℕ)^1024*400000000000000^4165 ≤ 400067857946531^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034507941726491181 50000000000000000000 400067857946531 400000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400067857946531/400000000000000 : ℝ)) (X := (50034507941726491181/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7061287290325911/50000000000000000000 : ℝ) ≤ ((578554088825798029/578750000000000000 : ℝ)+2*(167015342139/92600000000000 : ℝ)*(11309/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (578554088825798029/578750000000000000 : ℝ)+2*(167015342139/92600000000000 : ℝ)*(11309/100000 : ℝ)=(10000694356610441/10000000000000000 : ℝ) by norm_num, show 1+2*(7061287290325911/50000000000000000000 : ℝ)=(25007061287290325911/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34507941726491181/100000000000000000000 : ℝ)+(7061287290325911/50000000000000000000 : ℝ) ≤ ((578554088825798029/578750000000000000 : ℝ)+(167015342139/92600000000000 : ℝ)*((14087/100000 : ℝ)+(11309/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (578554088825798029/578750000000000000 : ℝ)+(167015342139/92600000000000 : ℝ)*((14087/100000 : ℝ)+(11309/100000 : ℝ))=(5000597701318429/5000000000000000 : ℝ) by norm_num, show 1+(34507941726491181/100000000000000000000 : ℝ)+(7061287290325911/50000000000000000000 : ℝ)=(100048630516307143003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34507941726491181/100000000000000000000 : ℝ) ≤ ((578554088825798029/578750000000000000 : ℝ)+2*(167015342139/92600000000000 : ℝ)*(14087/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (578554088825798029/578750000000000000 : ℝ)+2*(167015342139/92600000000000 : ℝ)*(14087/100000 : ℝ)=(400067857946531/400000000000000 : ℝ) by norm_num, show 1+2*(34507941726491181/100000000000000000000 : ℝ)=(50034507941726491181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (578554088825798029/578750000000000000 : ℝ)*(X 1 0+X 2 0)+(167015342139/92600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (578554088825798029/578750000000000000 : ℝ)) (alpha := (167015342139/92600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (578554088825798029/578750000000000000 : ℝ)*(X 0 1+X 2 1)+(167015342139/92600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (578554088825798029/578750000000000000 : ℝ)) (alpha := (167015342139/92600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (578554088825798029/578750000000000000 : ℝ)*(X 0 2+X 1 2)+(167015342139/92600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (578554088825798029/578750000000000000 : ℝ)) (alpha := (167015342139/92600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-17350167/80000000 : ℝ)*X 0 0+(539346153/1000000000 : ℝ)*X 0 1+(5265338459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344861579/10000000000 : ℝ)*X 1 0+(-2233763107/10000000000 : ℝ)*X 1 1+(131633461/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672430779/5000000000 : ℝ)*X 2 0+(5265338449/10000000000 : ℝ)*X 2 1+(-1116881561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365219291/10000000000 : ℝ)*X 0 0+(423972069/1000000000 : ℝ)*X 0 1+(2247209181/5000000000 : ℝ)*X 0 2+(4365219291/10000000000 : ℝ)*X 1 0+(423972069/1000000000 : ℝ)*X 1 1+(2247209181/5000000000 : ℝ)*X 1 2+(4365219291/10000000000 : ℝ)*X 2 0+(423972069/1000000000 : ℝ)*X 2 1+(2247209181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1084387977/5000000000 : ℝ)*X 0 0+(5265661899/10000000000 : ℝ)*X 0 1+(1078627367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656205347/5000000000 : ℝ)*X 1 0+(-2105964831/10000000000 : ℝ)*X 1 1+(5393136753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656205399/5000000000 : ℝ)*X 2 0+(5393136561/10000000000 : ℝ)*X 2 1+(-2105964951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873045811/2000000000 : ℝ)*X 0 0+(179751007/400000000 : ℝ)*X 0 1+(16563931/39062500 : ℝ)*X 0 2+(873045811/2000000000 : ℝ)*X 1 0+(179751007/400000000 : ℝ)*X 1 1+(16563931/39062500 : ℝ)*X 1 2+(873045811/2000000000 : ℝ)*X 2 0+(179751007/400000000 : ℝ)*X 2 1+(16563931/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17527041314328884612630691/7234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122997077/20000000000000 : ℝ)*(base19) + (273886733/50000000000000 : ℝ)*(base23) + (9766639/50000000000000 : ℝ)*(lower2) + (71035367/100000000000000 : ℝ)*(upper3) + (340999/2500000000000 : ℝ)*(upper5) + (1466409106108991/25000000000000 : ℝ)*(major0) + (1466409106108991/25000000000000 : ℝ)*(major1) + (1466409106108991/25000000000000 : ℝ)*(major2) + (7805014085839179/100000000000000 : ℝ)*(sp0) + (7805029535990693/100000000000000 : ℝ)*(sp1) + (7805029603202611/100000000000000 : ℝ)*(sp2) + (981558114937273/25000000000000 : ℝ)*(sp3) + (16065136899/100000000000000 : ℝ)*(sp4) + (10157388601/100000000000000 : ℝ)*(sp7) + (981560654284423/25000000000000 : ℝ)*(f.failure) + (7805030150976077/100000000000000 : ℝ)*(f.sum) + (1013993349321/1157500000000000000000000000 : ℝ)*base66 + (122150621946097489/14468750000000000000000000000000 : ℝ)*base67 + (189551350089222489/14468750000000000000000000000000 : ℝ)*base69 + (194499705879722489/14468750000000000000000000000000 : ℝ)*base71 + (2210191986631/1157500000000000000000000000 : ℝ)*base74 + (6397181802090011/14468750000000000000000000000000 : ℝ)*base76 + (245113654975566239/14468750000000000000000000000000 : ℝ)*base77 + (407924418537222489/14468750000000000000000000000000 : ℝ)*base79 + (76641365657/578750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (9636013/2500000000000000000000 : ℝ)*base90 + (9636013/2500000000000000000000 : ℝ)*base92 + (9636013/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (306015841736796293356324359/28937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2180681253/100000000000000 : ℝ)*(base19) + (2384823343/100000000000000 : ℝ)*(base23) + (52778073/100000000000000 : ℝ)*(upper2) + (86473009/50000000000000 : ℝ)*(upper3) + (1728041/625000000000 : ℝ)*(upper5) + (5895437229400243/100000000000000 : ℝ)*(major0) + (5895437229400243/100000000000000 : ℝ)*(major1) + (5895437229400243/100000000000000 : ℝ)*(major2) + (60042858819/100000000000000 : ℝ)*(sp1) + (6507177813/12500000000000 : ℝ)*(sp2) + (784468391962023/10000000000000 : ℝ)*(sp4) + (7844621696080159/100000000000000 : ℝ)*(sp5) + (490289342335899/6250000000000 : ℝ)*(sp6) + (1973095093339099/50000000000000 : ℝ)*(sp7) + (1973095093339099/50000000000000 : ℝ)*(f.failure) + (784468391962023/10000000000000 : ℝ)*(f.sum) + (34651836026323/4630000000000000000000000000 : ℝ)*base66 + (122558183287372703/57875000000000000000000000000000 : ℝ)*base68 + (313734636443377297/57875000000000000000000000000000 : ℝ)*base69 + (176260453103752297/57875000000000000000000000000000 : ℝ)*base71 + (23422986021663/4630000000000000000000000000 : ℝ)*base74 + (482352636552002297/57875000000000000000000000000000 : ℝ)*base75 + (107133982667622703/57875000000000000000000000000000 : ℝ)*base78 + (738408087231377297/57875000000000000000000000000000 : ℝ)*base79 + (35755333493503/4630000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11037769/5000000000000000000000 : ℝ)*base90 + (11037769/5000000000000000000000 : ℝ)*base92 + (11037769/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1138_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1138_s7_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168794471/10000000000 : ℝ)*x 0 + (674142027/1250000000 : ℝ)*x 1 + (329103041/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168794471/10000000000 : ℝ)^8331 ≤ (3294525403191/25000000000000 : ℝ)^6283 := by
    have hnat : (2168794471 : ℕ)^8331*25000000000000^6283 ≤ 3294525403191^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168794471 10000000000 3294525403191 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674142027/1250000000 : ℝ)^8331 ≤ (8819880270141/20000000000000 : ℝ)^6283 := by
    have hnat : (674142027 : ℕ)^8331*20000000000000^6283 ≤ 8819880270141^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674142027 1250000000 8819880270141 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329103041/625000000 : ℝ)^8331 ≤ (42722497029747/100000000000000 : ℝ)^6283 := by
    have hnat : (329103041 : ℕ)^8331*100000000000000^6283 ≤ 42722497029747^6283*625000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329103041 625000000 42722497029747 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168794471/10000000000 : ℝ), (674142027/1250000000 : ℝ), (329103041/625000000 : ℝ)] ![(3294525403191/25000000000000 : ℝ), (8819880270141/20000000000000 : ℝ), (42722497029747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168794471/10000000000 : ℝ)|^8331 ≤ (3294525403191/25000000000000 : ℝ)^6283
        have hw : |(-2168794471/10000000000 : ℝ)|=(2168794471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674142027/1250000000 : ℝ)|^8331 ≤ (8819880270141/20000000000000 : ℝ)^6283
        have hw : |(674142027/1250000000 : ℝ)|=(674142027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329103041/625000000 : ℝ)|^8331 ≤ (42722497029747/100000000000000 : ℝ)^6283
        have hw : |(329103041/625000000 : ℝ)|=(329103041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672390557/5000000000 : ℝ)*x 0 + (-89338391/400000000 : ℝ)*x 1 + (5265648659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672390557/5000000000 : ℝ)^8331 ≤ (21787944273843/50000000000000 : ℝ)^6283 := by
    have hnat : (2672390557 : ℕ)^8331*50000000000000^6283 ≤ 21787944273843^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672390557 5000000000 21787944273843 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89338391/400000000 : ℝ)^8331 ≤ (3425403592929/25000000000000 : ℝ)^6283 := by
    have hnat : (89338391 : ℕ)^8331*25000000000000^6283 ≤ 3425403592929^6283*400000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89338391 400000000 3425403592929 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265648659/10000000000 : ℝ)^8331 ≤ (42722497062021/100000000000000 : ℝ)^6283 := by
    have hnat : (5265648659 : ℕ)^8331*100000000000000^6283 ≤ 42722497062021^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265648659 10000000000 42722497062021 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672390557/5000000000 : ℝ), (-89338391/400000000 : ℝ), (5265648659/10000000000 : ℝ)] ![(21787944273843/50000000000000 : ℝ), (3425403592929/25000000000000 : ℝ), (42722497062021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672390557/5000000000 : ℝ)|^8331 ≤ (21787944273843/50000000000000 : ℝ)^6283
        have hw : |(2672390557/5000000000 : ℝ)|=(2672390557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89338391/400000000 : ℝ)|^8331 ≤ (3425403592929/25000000000000 : ℝ)^6283
        have hw : |(-89338391/400000000 : ℝ)|=(89338391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265648659/10000000000 : ℝ)|^8331 ≤ (42722497062021/100000000000000 : ℝ)^6283
        have hw : |(5265648659/10000000000 : ℝ)|=(5265648659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336195279/2500000000 : ℝ)*x 0 + (263282433/500000000 : ℝ)*x 1 + (-558364943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336195279/2500000000 : ℝ)^8331 ≤ (43575888569307/100000000000000 : ℝ)^6283 := by
    have hnat : (1336195279 : ℕ)^8331*100000000000000^6283 ≤ 43575888569307^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336195279 2500000000 43575888569307 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263282433/500000000 : ℝ)^8331 ≤ (42722497072779/100000000000000 : ℝ)^6283 := by
    have hnat : (263282433 : ℕ)^8331*100000000000000^6283 ≤ 42722497072779^6283*500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263282433 500000000 42722497072779 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558364943/2500000000 : ℝ)^8331 ≤ (13701614347313/100000000000000 : ℝ)^6283 := by
    have hnat : (558364943 : ℕ)^8331*100000000000000^6283 ≤ 13701614347313^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558364943 2500000000 13701614347313 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336195279/2500000000 : ℝ), (263282433/500000000 : ℝ), (-558364943/2500000000 : ℝ)] ![(43575888569307/100000000000000 : ℝ), (42722497072779/100000000000000 : ℝ), (13701614347313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336195279/2500000000 : ℝ)|^8331 ≤ (43575888569307/100000000000000 : ℝ)^6283
        have hw : |(1336195279/2500000000 : ℝ)|=(1336195279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263282433/500000000 : ℝ)|^8331 ≤ (42722497072779/100000000000000 : ℝ)^6283
        have hw : |(263282433/500000000 : ℝ)|=(263282433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558364943/2500000000 : ℝ)|^8331 ≤ (13701614347313/100000000000000 : ℝ)^6283
        have hw : |(-558364943/2500000000 : ℝ)|=(558364943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182617749/5000000000 : ℝ)*x 0 + (4240350311/10000000000 : ℝ)*x 1 + (2246892259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182617749/5000000000 : ℝ)^8331 ≤ (4164616129041/12500000000000 : ℝ)^6283 := by
    have hnat : (2182617749 : ℕ)^8331*12500000000000^6283 ≤ 4164616129041^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182617749 5000000000 4164616129041 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240350311/10000000000 : ℝ)^8331 ≤ (8014750581201/25000000000000 : ℝ)^6283 := by
    have hnat : (4240350311 : ℕ)^8331*25000000000000^6283 ≤ 8014750581201^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240350311 10000000000 8014750581201 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246892259/5000000000 : ℝ)^8331 ≤ (6924813726561/20000000000000 : ℝ)^6283 := by
    have hnat : (2246892259 : ℕ)^8331*20000000000000^6283 ≤ 6924813726561^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246892259 5000000000 6924813726561 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182617749/5000000000 : ℝ), (4240350311/10000000000 : ℝ), (2246892259/5000000000 : ℝ)] ![(4164616129041/12500000000000 : ℝ), (8014750581201/25000000000000 : ℝ), (6924813726561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182617749/5000000000 : ℝ)|^8331 ≤ (4164616129041/12500000000000 : ℝ)^6283
        have hw : |(2182617749/5000000000 : ℝ)|=(2182617749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240350311/10000000000 : ℝ)|^8331 ≤ (8014750581201/25000000000000 : ℝ)^6283
        have hw : |(4240350311/10000000000 : ℝ)|=(4240350311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246892259/5000000000 : ℝ)|^8331 ≤ (6924813726561/20000000000000 : ℝ)^6283
        have hw : |(2246892259/5000000000 : ℝ)|=(2246892259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168799003/10000000000 : ℝ)*x 0 + (5265971743/10000000000 : ℝ)*x 1 + (674101533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168799003/10000000000 : ℝ)^8331 ≤ (6589069063179/50000000000000 : ℝ)^6283 := by
    have hnat : (2168799003 : ℕ)^8331*50000000000000^6283 ≤ 6589069063179^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168799003 10000000000 6589069063179 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265971743/10000000000 : ℝ)^8331 ≤ (21362986430371/50000000000000 : ℝ)^6283 := by
    have hnat : (5265971743 : ℕ)^8331*50000000000000^6283 ≤ 21362986430371^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265971743 10000000000 21362986430371 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674101533/1250000000 : ℝ)^8331 ≤ (881917780013/2000000000000 : ℝ)^6283 := by
    have hnat : (674101533 : ℕ)^8331*2000000000000^6283 ≤ 881917780013^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674101533 1250000000 881917780013 2000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168799003/10000000000 : ℝ), (5265971743/10000000000 : ℝ), (674101533/1250000000 : ℝ)] ![(6589069063179/50000000000000 : ℝ), (21362986430371/50000000000000 : ℝ), (881917780013/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168799003/10000000000 : ℝ)|^8331 ≤ (6589069063179/50000000000000 : ℝ)^6283
        have hw : |(-2168799003/10000000000 : ℝ)|=(2168799003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265971743/10000000000 : ℝ)|^8331 ≤ (21362986430371/50000000000000 : ℝ)^6283
        have hw : |(5265971743/10000000000 : ℝ)|=(5265971743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674101533/1250000000 : ℝ)|^8331 ≤ (881917780013/2000000000000 : ℝ)^6283
        have hw : |(674101533/1250000000 : ℝ)|=(674101533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312489301/10000000000 : ℝ)*x 0 + (-1053146587/5000000000 : ℝ)*x 1 + (5392816859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312489301/10000000000 : ℝ)^8331 ≤ (10806785403799/25000000000000 : ℝ)^6283 := by
    have hnat : (5312489301 : ℕ)^8331*25000000000000^6283 ≤ 10806785403799^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312489301 10000000000 10806785403799 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053146587/5000000000 : ℝ)^8331 ≤ (3169229887339/25000000000000 : ℝ)^6283 := by
    have hnat : (1053146587 : ℕ)^8331*25000000000000^6283 ≤ 3169229887339^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053146587 5000000000 3169229887339 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392816859/10000000000 : ℝ)^8331 ≤ (8819187764009/20000000000000 : ℝ)^6283 := by
    have hnat : (5392816859 : ℕ)^8331*20000000000000^6283 ≤ 8819187764009^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392816859 10000000000 8819187764009 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312489301/10000000000 : ℝ), (-1053146587/5000000000 : ℝ), (5392816859/10000000000 : ℝ)] ![(10806785403799/25000000000000 : ℝ), (3169229887339/25000000000000 : ℝ), (8819187764009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312489301/10000000000 : ℝ)|^8331 ≤ (10806785403799/25000000000000 : ℝ)^6283
        have hw : |(5312489301/10000000000 : ℝ)|=(5312489301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053146587/5000000000 : ℝ)|^8331 ≤ (3169229887339/25000000000000 : ℝ)^6283
        have hw : |(-1053146587/5000000000 : ℝ)|=(1053146587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392816859/10000000000 : ℝ)|^8331 ≤ (8819187764009/20000000000000 : ℝ)^6283
        have hw : |(5392816859/10000000000 : ℝ)|=(5392816859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328122609/2500000000 : ℝ)*x 0 + (1348203773/2500000000 : ℝ)*x 1 + (-2106294041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328122609/2500000000 : ℝ)^8331 ≤ (43227153860919/100000000000000 : ℝ)^6283 := by
    have hnat : (1328122609 : ℕ)^8331*100000000000000^6283 ≤ 43227153860919^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328122609 2500000000 43227153860919 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348203773/2500000000 : ℝ)^8331 ≤ (22047959831037/50000000000000 : ℝ)^6283 := by
    have hnat : (1348203773 : ℕ)^8331*50000000000000^6283 ≤ 22047959831037^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348203773 2500000000 22047959831037 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106294041/10000000000 : ℝ)^8331 ≤ (12676926468369/100000000000000 : ℝ)^6283 := by
    have hnat : (2106294041 : ℕ)^8331*100000000000000^6283 ≤ 12676926468369^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106294041 10000000000 12676926468369 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328122609/2500000000 : ℝ), (1348203773/2500000000 : ℝ), (-2106294041/10000000000 : ℝ)] ![(43227153860919/100000000000000 : ℝ), (22047959831037/50000000000000 : ℝ), (12676926468369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328122609/2500000000 : ℝ)|^8331 ≤ (43227153860919/100000000000000 : ℝ)^6283
        have hw : |(1328122609/2500000000 : ℝ)|=(1328122609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348203773/2500000000 : ℝ)|^8331 ≤ (22047959831037/50000000000000 : ℝ)^6283
        have hw : |(1348203773/2500000000 : ℝ)|=(1348203773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106294041/10000000000 : ℝ)|^8331 ≤ (12676926468369/100000000000000 : ℝ)^6283
        have hw : |(-2106294041/10000000000 : ℝ)|=(2106294041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s7_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182622677/5000000000 : ℝ)*x 0 + (4493147911/10000000000 : ℝ)*x 1 + (4240989097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182622677/5000000000 : ℝ)^8331 ≤ (16658514388329/50000000000000 : ℝ)^6283 := by
    have hnat : (2182622677 : ℕ)^8331*50000000000000^6283 ≤ 16658514388329^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182622677 5000000000 16658514388329 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493147911/10000000000 : ℝ)^8331 ≤ (34617564980529/100000000000000 : ℝ)^6283 := by
    have hnat : (4493147911 : ℕ)^8331*100000000000000^6283 ≤ 34617564980529^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493147911 10000000000 34617564980529 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240989097/10000000000 : ℝ)^8331 ≤ (32065406222607/100000000000000 : ℝ)^6283 := by
    have hnat : (4240989097 : ℕ)^8331*100000000000000^6283 ≤ 32065406222607^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240989097 10000000000 32065406222607 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182622677/5000000000 : ℝ), (4493147911/10000000000 : ℝ), (4240989097/10000000000 : ℝ)] ![(16658514388329/50000000000000 : ℝ), (34617564980529/100000000000000 : ℝ), (32065406222607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182622677/5000000000 : ℝ)|^8331 ≤ (16658514388329/50000000000000 : ℝ)^6283
        have hw : |(2182622677/5000000000 : ℝ)|=(2182622677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493147911/10000000000 : ℝ)|^8331 ≤ (34617564980529/100000000000000 : ℝ)^6283
        have hw : |(4493147911/10000000000 : ℝ)|=(4493147911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240989097/10000000000 : ℝ)|^8331 ≤ (32065406222607/100000000000000 : ℝ)^6283
        have hw : |(4240989097/10000000000 : ℝ)|=(4240989097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11341/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2811/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11341/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2811/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11341/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (11341/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (3571454812614537/25000000000000000000 : ℝ) := by
    have hpowers : (11341/100000 : ℝ)^4165 ≤ (3571454812614537/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11341 : ℕ)^4165*25000000000000000000^1024 ≤ 3571454812614537^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11341 100000 3571454812614537 25000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11341/100000 : ℝ)) (X := (3571454812614537/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2811/20000 : ℝ) ^ (4165/1024 : ℝ) ≤ (34190216095619901/100000000000000000000 : ℝ) := by
    have hpowers : (2811/20000 : ℝ)^4165 ≤ (34190216095619901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2811 : ℕ)^4165*100000000000000000000^1024 ≤ 34190216095619901^1024*20000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 20000 34190216095619901 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/20000 : ℝ)) (X := (34190216095619901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503571454812614537/12500000000000000000 : ℝ) ≤ (10000702381903981/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (12503571454812614537/12500000000000000000 : ℝ)^1024 ≤ (10000702381903981/10000000000000000 : ℝ)^4165 := by
      have hnat : (12503571454812614537 : ℕ)^1024*10000000000000000^4165 ≤ 10000702381903981^4165*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503571454812614537 12500000000000000000 10000702381903981 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000702381903981/10000000000000000 : ℝ)) (X := (12503571454812614537/12500000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048476035346078049/100000000000000000000 : ℝ) ≤ (10001191605983643/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (100048476035346078049/100000000000000000000 : ℝ)^1024 ≤ (10001191605983643/10000000000000000 : ℝ)^4165 := by
      have hnat : (100048476035346078049 : ℕ)^1024*10000000000000000^4165 ≤ 10001191605983643^4165*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048476035346078049 100000000000000000000 10001191605983643 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001191605983643/10000000000000000 : ℝ)) (X := (100048476035346078049/100000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034190216095619901/50000000000000000000 : ℝ) ≤ (2000336166012661/2000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50034190216095619901/50000000000000000000 : ℝ)^1024 ≤ (2000336166012661/2000000000000000 : ℝ)^4165 := by
      have hnat : (50034190216095619901 : ℕ)^1024*2000000000000000^4165 ≤ 2000336166012661^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034190216095619901 50000000000000000000 2000336166012661 2000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000336166012661/2000000000000000 : ℝ)) (X := (50034190216095619901/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3571454812614537/25000000000000000000 : ℝ) ≤ ((542616193678250219/542800000000000000 : ℝ)+2*(244612039831/135700000000000 : ℝ)*(11341/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (542616193678250219/542800000000000000 : ℝ)+2*(244612039831/135700000000000 : ℝ)*(11341/100000 : ℝ)=(10000702381903981/10000000000000000 : ℝ) by norm_num, show 1+2*(3571454812614537/25000000000000000000 : ℝ)=(12503571454812614537/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34190216095619901/100000000000000000000 : ℝ)+(3571454812614537/25000000000000000000 : ℝ) ≤ ((542616193678250219/542800000000000000 : ℝ)+(244612039831/135700000000000 : ℝ)*((2811/20000 : ℝ)+(11341/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (542616193678250219/542800000000000000 : ℝ)+(244612039831/135700000000000 : ℝ)*((2811/20000 : ℝ)+(11341/100000 : ℝ))=(10001191605983643/10000000000000000 : ℝ) by norm_num, show 1+(34190216095619901/100000000000000000000 : ℝ)+(3571454812614537/25000000000000000000 : ℝ)=(100048476035346078049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34190216095619901/100000000000000000000 : ℝ) ≤ ((542616193678250219/542800000000000000 : ℝ)+2*(244612039831/135700000000000 : ℝ)*(2811/20000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (542616193678250219/542800000000000000 : ℝ)+2*(244612039831/135700000000000 : ℝ)*(2811/20000 : ℝ)=(2000336166012661/2000000000000000 : ℝ) by norm_num, show 1+2*(34190216095619901/100000000000000000000 : ℝ)=(50034190216095619901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (542616193678250219/542800000000000000 : ℝ)*(X 1 0+X 2 0)+(244612039831/135700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (542616193678250219/542800000000000000 : ℝ)) (alpha := (244612039831/135700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (542616193678250219/542800000000000000 : ℝ)*(X 0 1+X 2 1)+(244612039831/135700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (542616193678250219/542800000000000000 : ℝ)) (alpha := (244612039831/135700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (542616193678250219/542800000000000000 : ℝ)*(X 0 2+X 1 2)+(244612039831/135700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11341/100000 : ℝ)) (hi := (2811/20000 : ℝ)) (c := (542616193678250219/542800000000000000 : ℝ)) (alpha := (244612039831/135700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2168794471/10000000000 : ℝ)*X 0 0+(674142027/1250000000 : ℝ)*X 0 1+(329103041/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672390557/5000000000 : ℝ)*X 1 0+(-89338391/400000000 : ℝ)*X 1 1+(5265648659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336195279/2500000000 : ℝ)*X 2 0+(263282433/500000000 : ℝ)*X 2 1+(-558364943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182617749/5000000000 : ℝ)*X 0 0+(4240350311/10000000000 : ℝ)*X 0 1+(2246892259/5000000000 : ℝ)*X 0 2+(2182617749/5000000000 : ℝ)*X 1 0+(4240350311/10000000000 : ℝ)*X 1 1+(2246892259/5000000000 : ℝ)*X 1 2+(2182617749/5000000000 : ℝ)*X 2 0+(4240350311/10000000000 : ℝ)*X 2 1+(2246892259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2168799003/10000000000 : ℝ)*X 0 0+(5265971743/10000000000 : ℝ)*X 0 1+(674101533/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312489301/10000000000 : ℝ)*X 1 0+(-1053146587/5000000000 : ℝ)*X 1 1+(5392816859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328122609/2500000000 : ℝ)*X 2 0+(1348203773/2500000000 : ℝ)*X 2 1+(-2106294041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182622677/5000000000 : ℝ)*X 0 0+(4493147911/10000000000 : ℝ)*X 0 1+(4240989097/10000000000 : ℝ)*X 0 2+(2182622677/5000000000 : ℝ)*X 1 0+(4493147911/10000000000 : ℝ)*X 1 1+(4240989097/10000000000 : ℝ)*X 1 2+(2182622677/5000000000 : ℝ)*X 2 0+(4493147911/10000000000 : ℝ)*X 2 1+(4240989097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112483352097497847294813609/13570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1639963907/100000000000000 : ℝ)*(base19) + (1533858531/100000000000000 : ℝ)*(base23) + (58279801/100000000000000 : ℝ)*(lower2) + (206104381/100000000000000 : ℝ)*(upper3) + (131422767/100000000000000 : ℝ)*(upper5) + (5894918978188937/100000000000000 : ℝ)*(major0) + (5894918978188937/100000000000000 : ℝ)*(major1) + (5894918978188937/100000000000000 : ℝ)*(major2) + (3921974679034041/50000000000000 : ℝ)*(sp0) + (1960998187962273/25000000000000 : ℝ)*(sp1) + (7843992857954467/100000000000000 : ℝ)*(sp2) + (789163832398587/20000000000000 : ℝ)*(sp3) + (45033744917/100000000000000 : ℝ)*(sp4) + (24126267943/100000000000000 : ℝ)*(sp7) + (1972921644130439/50000000000000 : ℝ)*(f.failure) + (3921997195906499/50000000000000 : ℝ)*(f.sum) + (2205781278579/848125000000000000000000000 : ℝ)*base65 + (857267722924064797/54280000000000000000000000000000 : ℝ)*base68 + (922211016982464797/54280000000000000000000000000000 : ℝ)*base70 + (947624058560984797/54280000000000000000000000000000 : ℝ)*base72 + (25968090188617/6785000000000000000000000000 : ℝ)*base73 + (1469087865543904797/54280000000000000000000000000000 : ℝ)*base76 + (132016177431495203/54280000000000000000000000000000 : ℝ)*base77 + (1415256687811624797/54280000000000000000000000000000 : ℝ)*base80 + (3531665094899/3392500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7668691/5000000000000000000000 : ℝ)*base89 + (7668691/5000000000000000000000 : ℝ)*base91 + (7668691/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (178496779199313720742911069/13570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1182267987/100000000000000 : ℝ)*(base15) + (294034169/100000000000000 : ℝ)*(lower2) + (5554139/2000000000000 : ℝ)*(upper3) + (5405943/4000000000000 : ℝ)*(lower4) + (5924906815766717/100000000000000 : ℝ)*(major0) + (5924906815766717/100000000000000 : ℝ)*(major1) + (5924906815766717/100000000000000 : ℝ)*(major2) + (42579328999/20000000000000 : ℝ)*(sp1) + (9788709127/6250000000000 : ℝ)*(sp2) + (15854445569/20000000000000 : ℝ)*(sp3) + (985487142809729/12500000000000 : ℝ)*(sp4) + (7883683063564851/100000000000000 : ℝ)*(sp5) + (39418702615659/500000000000 : ℝ)*(sp6) + (991459194592113/25000000000000 : ℝ)*(sp7) + (1982958025298149/50000000000000 : ℝ)*(f.failure) + (985487142809729/12500000000000 : ℝ)*(f.sum) + (30890624500057/6785000000000000000000000000 : ℝ)*base65 + (293203878372570977/54280000000000000000000000000000 : ℝ)*base68 + (120647131927090977/54280000000000000000000000000000 : ℝ)*base70 + (413929763059749023/54280000000000000000000000000000 : ℝ)*base71 + (48494320257947/6785000000000000000000000000 : ℝ)*base73 + (819540294349570977/54280000000000000000000000000000 : ℝ)*base76 + (89507082834930977/54280000000000000000000000000000 : ℝ)*base78 + (364112097380890977/54280000000000000000000000000000 : ℝ)*base80 + (38674168010577/6785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (44316681/5000000000000000000000 : ℝ)*base89 + (44316681/5000000000000000000000 : ℝ)*base91 + (44316681/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1138_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2811/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11341/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1138_s8_0 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168802427/10000000000 : ℝ)*x 0 + (5393069369/10000000000 : ℝ)*x 1 + (5265710067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168802427/10000000000 : ℝ)^8331 ≤ (1317816571299/10000000000000 : ℝ)^6283 := by
    have hnat : (2168802427 : ℕ)^8331*10000000000000^6283 ≤ 1317816571299^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168802427 10000000000 1317816571299 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393069369/10000000000 : ℝ)^8331 ≤ (44098676577009/100000000000000 : ℝ)^6283 := by
    have hnat : (5393069369 : ℕ)^8331*100000000000000^6283 ≤ 44098676577009^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393069369 10000000000 44098676577009 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265710067/10000000000 : ℝ)^8331 ≤ (21361578847769/50000000000000 : ℝ)^6283 := by
    have hnat : (5265710067 : ℕ)^8331*50000000000000^6283 ≤ 21361578847769^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265710067 10000000000 21361578847769 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168802427/10000000000 : ℝ), (5393069369/10000000000 : ℝ), (5265710067/10000000000 : ℝ)] ![(1317816571299/10000000000000 : ℝ), (44098676577009/100000000000000 : ℝ), (21361578847769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168802427/10000000000 : ℝ)|^8331 ≤ (1317816571299/10000000000000 : ℝ)^6283
        have hw : |(-2168802427/10000000000 : ℝ)|=(2168802427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393069369/10000000000 : ℝ)|^8331 ≤ (44098676577009/100000000000000 : ℝ)^6283
        have hw : |(5393069369/10000000000 : ℝ)|=(5393069369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265710067/10000000000 : ℝ)|^8331 ≤ (21361578847769/50000000000000 : ℝ)^6283
        have hw : |(5265710067/10000000000 : ℝ)|=(5265710067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_1 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344763653/10000000000 : ℝ)*x 0 + (-2233401759/10000000000 : ℝ)*x 1 + (5265710071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344763653/10000000000 : ℝ)^8331 ≤ (1361740618293/3125000000000 : ℝ)^6283 := by
    have hnat : (5344763653 : ℕ)^8331*3125000000000^6283 ≤ 1361740618293^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344763653 10000000000 1361740618293 3125000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233401759/10000000000 : ℝ)^8331 ≤ (214080350787/1562500000000 : ℝ)^6283 := by
    have hnat : (2233401759 : ℕ)^8331*1562500000000^6283 ≤ 214080350787^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233401759 10000000000 214080350787 1562500000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265710071/10000000000 : ℝ)^8331 ≤ (4272315773857/10000000000000 : ℝ)^6283 := by
    have hnat : (5265710071 : ℕ)^8331*10000000000000^6283 ≤ 4272315773857^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265710071 10000000000 4272315773857 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344763653/10000000000 : ℝ), (-2233401759/10000000000 : ℝ), (5265710071/10000000000 : ℝ)] ![(1361740618293/3125000000000 : ℝ), (214080350787/1562500000000 : ℝ), (4272315773857/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344763653/10000000000 : ℝ)|^8331 ≤ (1361740618293/3125000000000 : ℝ)^6283
        have hw : |(5344763653/10000000000 : ℝ)|=(5344763653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233401759/10000000000 : ℝ)|^8331 ≤ (214080350787/1562500000000 : ℝ)^6283
        have hw : |(-2233401759/10000000000 : ℝ)|=(2233401759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265710071/10000000000 : ℝ)|^8331 ≤ (4272315773857/10000000000000 : ℝ)^6283
        have hw : |(5265710071/10000000000 : ℝ)|=(5265710071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_2 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106895273/200000000 : ℝ)*x 0 + (5265710081/10000000000 : ℝ)*x 1 + (-2233401751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106895273/200000000 : ℝ)^8331 ≤ (8715139950589/20000000000000 : ℝ)^6283 := by
    have hnat : (106895273 : ℕ)^8331*20000000000000^6283 ≤ 8715139950589^6283*200000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106895273 200000000 8715139950589 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265710081/10000000000 : ℝ)^8331 ≤ (5340394730769/12500000000000 : ℝ)^6283 := by
    have hnat : (5265710081 : ℕ)^8331*12500000000000^6283 ≤ 5340394730769^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265710081 10000000000 5340394730769 12500000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2233401751/10000000000 : ℝ)^8331 ≤ (6850571192647/50000000000000 : ℝ)^6283 := by
    have hnat : (2233401751 : ℕ)^8331*50000000000000^6283 ≤ 6850571192647^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233401751 10000000000 6850571192647 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106895273/200000000 : ℝ), (5265710081/10000000000 : ℝ), (-2233401751/10000000000 : ℝ)] ![(8715139950589/20000000000000 : ℝ), (5340394730769/12500000000000 : ℝ), (6850571192647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106895273/200000000 : ℝ)|^8331 ≤ (8715139950589/20000000000000 : ℝ)^6283
        have hw : |(106895273/200000000 : ℝ)|=(106895273/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265710081/10000000000 : ℝ)|^8331 ≤ (5340394730769/12500000000000 : ℝ)^6283
        have hw : |(5265710081/10000000000 : ℝ)|=(5265710081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2233401751/10000000000 : ℝ)|^8331 ≤ (6850571192647/50000000000000 : ℝ)^6283
        have hw : |(-2233401751/10000000000 : ℝ)|=(2233401751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_3 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365238759/10000000000 : ℝ)*x 0 + (4240477369/10000000000 : ℝ)*x 1 + (449365661/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365238759/10000000000 : ℝ)^8331 ≤ (8329240508543/25000000000000 : ℝ)^6283 := by
    have hnat : (4365238759 : ℕ)^8331*25000000000000^6283 ≤ 8329240508543^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365238759 10000000000 8329240508543 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240477369/10000000000 : ℝ)^8331 ≤ (16030138034879/50000000000000 : ℝ)^6283 := by
    have hnat : (4240477369 : ℕ)^8331*50000000000000^6283 ≤ 16030138034879^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240477369 10000000000 16030138034879 50000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449365661/1000000000 : ℝ)^8331 ≤ (6924552377093/20000000000000 : ℝ)^6283 := by
    have hnat : (449365661 : ℕ)^8331*20000000000000^6283 ≤ 6924552377093^6283*1000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449365661 1000000000 6924552377093 20000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365238759/10000000000 : ℝ), (4240477369/10000000000 : ℝ), (449365661/1000000000 : ℝ)] ![(8329240508543/25000000000000 : ℝ), (16030138034879/50000000000000 : ℝ), (6924552377093/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365238759/10000000000 : ℝ)|^8331 ≤ (8329240508543/25000000000000 : ℝ)^6283
        have hw : |(4365238759/10000000000 : ℝ)|=(4365238759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240477369/10000000000 : ℝ)|^8331 ≤ (16030138034879/50000000000000 : ℝ)^6283
        have hw : |(4240477369/10000000000 : ℝ)|=(4240477369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449365661/1000000000 : ℝ)|^8331 ≤ (6924552377093/20000000000000 : ℝ)^6283
        have hw : |(449365661/1000000000 : ℝ)|=(449365661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_4 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2168807327/10000000000 : ℝ)*x 0 + (5266029709/10000000000 : ℝ)*x 1 + (67409357/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168807327/10000000000 : ℝ)^8331 ≤ (13178205191549/100000000000000 : ℝ)^6283 := by
    have hnat : (2168807327 : ℕ)^8331*100000000000000^6283 ≤ 13178205191549^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168807327 10000000000 13178205191549 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266029709/10000000000 : ℝ)^8331 ≤ (42726596477277/100000000000000 : ℝ)^6283 := by
    have hnat : (5266029709 : ℕ)^8331*100000000000000^6283 ≤ 42726596477277^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266029709 10000000000 42726596477277 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67409357/125000000 : ℝ)^8331 ≤ (44095198317689/100000000000000 : ℝ)^6283 := by
    have hnat : (67409357 : ℕ)^8331*100000000000000^6283 ≤ 44095198317689^6283*125000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67409357 125000000 44095198317689 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2168807327/10000000000 : ℝ), (5266029709/10000000000 : ℝ), (67409357/125000000 : ℝ)] ![(13178205191549/100000000000000 : ℝ), (42726596477277/100000000000000 : ℝ), (44095198317689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2168807327/10000000000 : ℝ)|^8331 ≤ (13178205191549/100000000000000 : ℝ)^6283
        have hw : |(-2168807327/10000000000 : ℝ)|=(2168807327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266029709/10000000000 : ℝ)|^8331 ≤ (42726596477277/100000000000000 : ℝ)^6283
        have hw : |(5266029709/10000000000 : ℝ)|=(5266029709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67409357/125000000 : ℝ)|^8331 ≤ (44095198317689/100000000000000 : ℝ)^6283
        have hw : |(67409357/125000000 : ℝ)|=(67409357/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_5 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328126547/2500000000 : ℝ)*x 0 + (-526590767/2500000000 : ℝ)*x 1 + (84261697/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328126547/2500000000 : ℝ)^8331 ≤ (4322732381221/10000000000000 : ℝ)^6283 := by
    have hnat : (1328126547 : ℕ)^8331*10000000000000^6283 ≤ 4322732381221^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328126547 2500000000 4322732381221 10000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526590767/2500000000 : ℝ)^8331 ≤ (12677477334873/100000000000000 : ℝ)^6283 := by
    have hnat : (526590767 : ℕ)^8331*100000000000000^6283 ≤ 12677477334873^6283*2500000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526590767 2500000000 12677477334873 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84261697/156250000 : ℝ)^8331 ≤ (44095198838107/100000000000000 : ℝ)^6283 := by
    have hnat : (84261697 : ℕ)^8331*100000000000000^6283 ≤ 44095198838107^6283*156250000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84261697 156250000 44095198838107 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328126547/2500000000 : ℝ), (-526590767/2500000000 : ℝ), (84261697/156250000 : ℝ)] ![(4322732381221/10000000000000 : ℝ), (12677477334873/100000000000000 : ℝ), (44095198838107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328126547/2500000000 : ℝ)|^8331 ≤ (4322732381221/10000000000000 : ℝ)^6283
        have hw : |(1328126547/2500000000 : ℝ)|=(1328126547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-526590767/2500000000 : ℝ)|^8331 ≤ (12677477334873/100000000000000 : ℝ)^6283
        have hw : |(-526590767/2500000000 : ℝ)|=(526590767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84261697/156250000 : ℝ)|^8331 ≤ (44095198838107/100000000000000 : ℝ)^6283
        have hw : |(84261697/156250000 : ℝ)|=(84261697/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_6 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312505733/10000000000 : ℝ)*x 0 + (674093557/1250000000 : ℝ)*x 1 + (-2106363889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312505733/10000000000 : ℝ)^8331 ≤ (43227318903127/100000000000000 : ℝ)^6283 := by
    have hnat : (5312505733 : ℕ)^8331*100000000000000^6283 ≤ 43227318903127^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312505733 10000000000 43227318903127 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674093557/1250000000 : ℝ)^8331 ≤ (11023799297529/25000000000000 : ℝ)^6283 := by
    have hnat : (674093557 : ℕ)^8331*25000000000000^6283 ≤ 11023799297529^6283*1250000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674093557 1250000000 11023799297529 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2106363889/10000000000 : ℝ)^8331 ≤ (12677483886857/100000000000000 : ℝ)^6283 := by
    have hnat : (2106363889 : ℕ)^8331*100000000000000^6283 ≤ 12677483886857^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106363889 10000000000 12677483886857 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312505733/10000000000 : ℝ), (674093557/1250000000 : ℝ), (-2106363889/10000000000 : ℝ)] ![(43227318903127/100000000000000 : ℝ), (11023799297529/25000000000000 : ℝ), (12677483886857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312505733/10000000000 : ℝ)|^8331 ≤ (43227318903127/100000000000000 : ℝ)^6283
        have hw : |(5312505733/10000000000 : ℝ)|=(5312505733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674093557/1250000000 : ℝ)|^8331 ≤ (11023799297529/25000000000000 : ℝ)^6283
        have hw : |(674093557/1250000000 : ℝ)|=(674093557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2106363889/10000000000 : ℝ)|^8331 ≤ (12677483886857/100000000000000 : ℝ)^6283
        have hw : |(-2106363889/10000000000 : ℝ)|=(2106363889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1138_s8_7 (p : ℝ) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182623993/5000000000 : ℝ)*x 0 + (2246510517/5000000000 : ℝ)*x 1 + (4241115727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182623993/5000000000 : ℝ)^8331 ≤ (1665852770647/5000000000000 : ℝ)^6283 := by
    have hnat : (2182623993 : ℕ)^8331*5000000000000^6283 ≤ 1665852770647^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182623993 5000000000 1665852770647 5000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246510517/5000000000 : ℝ)^8331 ≤ (8654067206503/25000000000000 : ℝ)^6283 := by
    have hnat : (2246510517 : ℕ)^8331*25000000000000^6283 ≤ 8654067206503^6283*5000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246510517 5000000000 8654067206503 25000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241115727/10000000000 : ℝ)^8331 ≤ (32066675739211/100000000000000 : ℝ)^6283 := by
    have hnat : (4241115727 : ℕ)^8331*100000000000000^6283 ≤ 32066675739211^6283*10000000000^8331 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241115727 10000000000 32066675739211 100000000000000 8331 6283 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8331/2048 : ℝ)) 8331 6283 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182623993/5000000000 : ℝ), (2246510517/5000000000 : ℝ), (4241115727/10000000000 : ℝ)] ![(1665852770647/5000000000000 : ℝ), (8654067206503/25000000000000 : ℝ), (32066675739211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182623993/5000000000 : ℝ)|^8331 ≤ (1665852770647/5000000000000 : ℝ)^6283
        have hw : |(2182623993/5000000000 : ℝ)|=(2182623993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246510517/5000000000 : ℝ)|^8331 ≤ (8654067206503/25000000000000 : ℝ)^6283
        have hw : |(2246510517/5000000000 : ℝ)|=(2246510517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241115727/10000000000 : ℝ)|^8331 ≤ (32066675739211/100000000000000 : ℝ)^6283
        have hw : |(4241115727/10000000000 : ℝ)|=(4241115727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1138_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11347/100000 : ℝ) ^ (4165/1024 : ℝ) ≤ (14316585352376841/100000000000000000000 : ℝ) := by
    have hpowers : (11347/100000 : ℝ)^4165 ≤ (14316585352376841/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11347 : ℕ)^4165*100000000000000000000^1024 ≤ 14316585352376841^1024*100000^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11347 100000 14316585352376841 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11347/100000 : ℝ)) (X := (14316585352376841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (4165/1024 : ℝ) ≤ (34121008726762721/100000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^4165 ≤ (34121008726762721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (439 : ℕ)^4165*100000000000000000000^1024 ≤ 34121008726762721^1024*3125^4165 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 34121008726762721 100000000000000000000 4165 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (34121008726762721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014316585352376841/50000000000000000000 : ℝ) ≤ (10000703894398313/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50014316585352376841/50000000000000000000 : ℝ)^1024 ≤ (10000703894398313/10000000000000000 : ℝ)^4165 := by
      have hnat : (50014316585352376841 : ℕ)^1024*10000000000000000^4165 ≤ 10000703894398313^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014316585352376841 50000000000000000000 10000703894398313 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000703894398313/10000000000000000 : ℝ)) (X := (50014316585352376841/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024218797039569781/50000000000000000000 : ℝ) ≤ (40004762644873/40000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50024218797039569781/50000000000000000000 : ℝ)^1024 ≤ (40004762644873/40000000000000 : ℝ)^4165 := by
      have hnat : (50024218797039569781 : ℕ)^1024*40000000000000^4165 ≤ 40004762644873^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024218797039569781 50000000000000000000 40004762644873 40000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40004762644873/40000000000000 : ℝ)) (X := (50024218797039569781/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034121008726762721/50000000000000000000 : ℝ) ≤ (10001677428038187/10000000000000000 : ℝ) ^ (4165/1024 : ℝ) := by
    have hpowers : (50034121008726762721/50000000000000000000 : ℝ)^1024 ≤ (10001677428038187/10000000000000000 : ℝ)^4165 := by
      have hnat : (50034121008726762721 : ℕ)^1024*10000000000000000^4165 ≤ 10001677428038187^4165*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034121008726762721 50000000000000000000 10001677428038187 10000000000000000 1024 4165 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001677428038187/10000000000000000 : ℝ)) (X := (50034121008726762721/50000000000000000000 : ℝ)) (by norm_num) 4165 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14316585352376841/100000000000000000000 : ℝ) ≤ ((5400170906511638627/5402000000000000000 : ℝ)+2*(486766819937/270100000000000 : ℝ)*(11347/100000 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (5400170906511638627/5402000000000000000 : ℝ)+2*(486766819937/270100000000000 : ℝ)*(11347/100000 : ℝ)=(10000703894398313/10000000000000000 : ℝ) by norm_num, show 1+2*(14316585352376841/100000000000000000000 : ℝ)=(50014316585352376841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34121008726762721/100000000000000000000 : ℝ)+(14316585352376841/100000000000000000000 : ℝ) ≤ ((5400170906511638627/5402000000000000000 : ℝ)+(486766819937/270100000000000 : ℝ)*((439/3125 : ℝ)+(11347/100000 : ℝ)))^(4165/1024 : ℝ) := by
    rw [show (5400170906511638627/5402000000000000000 : ℝ)+(486766819937/270100000000000 : ℝ)*((439/3125 : ℝ)+(11347/100000 : ℝ))=(40004762644873/40000000000000 : ℝ) by norm_num, show 1+(34121008726762721/100000000000000000000 : ℝ)+(14316585352376841/100000000000000000000 : ℝ)=(50024218797039569781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34121008726762721/100000000000000000000 : ℝ) ≤ ((5400170906511638627/5402000000000000000 : ℝ)+2*(486766819937/270100000000000 : ℝ)*(439/3125 : ℝ))^(4165/1024 : ℝ) := by
    rw [show (5400170906511638627/5402000000000000000 : ℝ)+2*(486766819937/270100000000000 : ℝ)*(439/3125 : ℝ)=(10001677428038187/10000000000000000 : ℝ) by norm_num, show 1+2*(34121008726762721/100000000000000000000 : ℝ)=(50034121008726762721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5400170906511638627/5402000000000000000 : ℝ)*(X 1 0+X 2 0)+(486766819937/270100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (5400170906511638627/5402000000000000000 : ℝ)) (alpha := (486766819937/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5400170906511638627/5402000000000000000 : ℝ)*(X 0 1+X 2 1)+(486766819937/270100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (5400170906511638627/5402000000000000000 : ℝ)) (alpha := (486766819937/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5400170906511638627/5402000000000000000 : ℝ)*(X 0 2+X 1 2)+(486766819937/270100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4165/1024 : ℝ)) (lo := (11347/100000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (5400170906511638627/5402000000000000000 : ℝ)) (alpha := (486766819937/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2168802427/10000000000 : ℝ)*X 0 0+(5393069369/10000000000 : ℝ)*X 0 1+(5265710067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344763653/10000000000 : ℝ)*X 1 0+(-2233401759/10000000000 : ℝ)*X 1 1+(5265710071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106895273/200000000 : ℝ)*X 2 0+(5265710081/10000000000 : ℝ)*X 2 1+(-2233401751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365238759/10000000000 : ℝ)*X 0 0+(4240477369/10000000000 : ℝ)*X 0 1+(449365661/1000000000 : ℝ)*X 0 2+(4365238759/10000000000 : ℝ)*X 1 0+(4240477369/10000000000 : ℝ)*X 1 1+(449365661/1000000000 : ℝ)*X 1 2+(4365238759/10000000000 : ℝ)*X 2 0+(4240477369/10000000000 : ℝ)*X 2 1+(449365661/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2168807327/10000000000 : ℝ)*X 0 0+(5266029709/10000000000 : ℝ)*X 0 1+(67409357/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328126547/2500000000 : ℝ)*X 1 0+(-526590767/2500000000 : ℝ)*X 1 1+(84261697/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312505733/10000000000 : ℝ)*X 2 0+(674093557/1250000000 : ℝ)*X 2 1+(-2106363889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182623993/5000000000 : ℝ)*X 0 0+(2246510517/5000000000 : ℝ)*X 0 1+(4241115727/10000000000 : ℝ)*X 0 2+(2182623993/5000000000 : ℝ)*X 1 0+(2246510517/5000000000 : ℝ)*X 1 1+(4241115727/10000000000 : ℝ)*X 1 2+(2182623993/5000000000 : ℝ)*X 2 0+(2246510517/5000000000 : ℝ)*X 2 1+(4241115727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1138_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (263491060905167019680709921/135050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (375558761/100000000000000 : ℝ)*(base19) + (78898351/25000000000000 : ℝ)*(base23) + (742363/2500000000000 : ℝ)*(lower2) + (19017/40000000000 : ℝ)*(upper3) + (4823749/25000000000000 : ℝ)*(upper5) + (2950401230305159/50000000000000 : ℝ)*(major0) + (2950401230305159/50000000000000 : ℝ)*(major1) + (2950401230305159/50000000000000 : ℝ)*(major2) + (3925906439601109/50000000000000 : ℝ)*(sp0) + (3925911502145191/50000000000000 : ℝ)*(sp1) + (392591153212787/5000000000000 : ℝ)*(sp2) + (1974887879579777/50000000000000 : ℝ)*(sp3) + (5250323463/50000000000000 : ℝ)*(sp4) + (357323531/6250000000000 : ℝ)*(sp7) + (78995629526721/2000000000000 : ℝ)*(f.failure) + (981477922481143/12500000000000 : ℝ)*(f.sum) + (130282980317/26376953125000000000000000 : ℝ)*base66 + (893616495905163307/270100000000000000000000000000000 : ℝ)*base68 + (3299733425011636693/270100000000000000000000000000000 : ℝ)*base69 + (401991474917363307/270100000000000000000000000000000 : ℝ)*base72 + (23878453858103/6752500000000000000000000000 : ℝ)*base73 + (6757126338696036693/270100000000000000000000000000000 : ℝ)*base75 + (493453348947236693/270100000000000000000000000000000 : ℝ)*base77 + (2943983220818436693/270100000000000000000000000000000 : ℝ)*base79 + (5246041299503/6752500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1171349/200000000000000000000 : ℝ)*base89 + (1171349/200000000000000000000 : ℝ)*base91 + (1171349/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1570812439437505247007443367/270100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164508981/50000000000000 : ℝ)*(base19) + (18606019/12500000000000 : ℝ)*(upper1) + (228271581/100000000000000 : ℝ)*(upper2) + (5438339/12500000000000 : ℝ)*(upper3) + (2563607/3125000000000 : ℝ)*(lower4) + (5930626401896207/100000000000000 : ℝ)*(major0) + (5930626401896207/100000000000000 : ℝ)*(major1) + (5930626401896207/100000000000000 : ℝ)*(major2) + (7932621701/50000000000000 : ℝ)*(sp0) + (19535693549/50000000000000 : ℝ)*(sp1) + (986436526526099/12500000000000 : ℝ)*(sp4) + (7891468677047133/100000000000000 : ℝ)*(sp5) + (3945754038726097/50000000000000 : ℝ)*(sp6) + (62027258320071/1562500000000 : ℝ)*(sp7) + (62027258320071/1562500000000 : ℝ)*(f.failure) + (3945754038726097/50000000000000 : ℝ)*(f.sum) + (45119973344229/13505000000000000000000000000 : ℝ)*base65 + (5825897313027232211/540200000000000000000000000000000 : ℝ)*base68 + (1312870733743232211/540200000000000000000000000000000 : ℝ)*base70 + (2843133419568767789/540200000000000000000000000000000 : ℝ)*base71 + (33977951711391/13505000000000000000000000000 : ℝ)*base74 + (2998368939936832211/540200000000000000000000000000000 : ℝ)*base76 + (36689515565367967789/540200000000000000000000000000000 : ℝ)*base77 + (2243700167466832211/540200000000000000000000000000000 : ℝ)*base80 + (93333668523151/13505000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (265001/156250000000000000000 : ℝ)*base90 + (265001/156250000000000000000 : ℝ)*base92 + (265001/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1138_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1138_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1138_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1138_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1138_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1138_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4165/1024 : ℝ) ≤ p) (hpb : p ≤ (8331/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149395669/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1138_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
