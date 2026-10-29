-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1673_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:15.803805+00:00
-- url     : https://prove2.me/submissions/1db82339-1e11-4f45-b538-80714d5b3b9b

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
theorem support_rectangle_w1673_s0_0 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-726569281/5000000000 : ℝ)*x 0 + (5757521083/10000000000 : ℝ)*x 1 + (2468370561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726569281/5000000000 : ℝ)^5011 ≤ (8854384839833/100000000000000 : ℝ)^3987 := by
    have hnat : (726569281 : ℕ)^5011*100000000000000^3987 ≤ 8854384839833^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726569281 5000000000 8854384839833 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5757521083/10000000000 : ℝ)^5011 ≤ (4996382745943/10000000000000 : ℝ)^3987 := by
    have hnat : (5757521083 : ℕ)^5011*10000000000000^3987 ≤ 4996382745943^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5757521083 10000000000 4996382745943 10000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2468370561/5000000000 : ℝ)^5011 ≤ (20590893837777/50000000000000 : ℝ)^3987 := by
    have hnat : (2468370561 : ℕ)^5011*50000000000000^3987 ≤ 20590893837777^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468370561 5000000000 20590893837777 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-726569281/5000000000 : ℝ), (5757521083/10000000000 : ℝ), (2468370561/5000000000 : ℝ)] ![(8854384839833/100000000000000 : ℝ), (4996382745943/10000000000000 : ℝ), (20590893837777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-726569281/5000000000 : ℝ)|^5011 ≤ (8854384839833/100000000000000 : ℝ)^3987
        have hw : |(-726569281/5000000000 : ℝ)|=(726569281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5757521083/10000000000 : ℝ)|^5011 ≤ (4996382745943/10000000000000 : ℝ)^3987
        have hw : |(5757521083/10000000000 : ℝ)|=(5757521083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2468370561/5000000000 : ℝ)|^5011 ≤ (20590893837777/50000000000000 : ℝ)^3987
        have hw : |(2468370561/5000000000 : ℝ)|=(2468370561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_1 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2714263627/5000000000 : ℝ)*x 0 + (-1901626453/10000000000 : ℝ)*x 1 + (30854639/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2714263627/5000000000 : ℝ)^5011 ≤ (23201131219733/50000000000000 : ℝ)^3987 := by
    have hnat : (2714263627 : ℕ)^5011*50000000000000^3987 ≤ 23201131219733^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714263627 5000000000 23201131219733 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1901626453/10000000000 : ℝ)^5011 ≤ (6207969074911/50000000000000 : ℝ)^3987 := by
    have hnat : (1901626453 : ℕ)^5011*50000000000000^3987 ≤ 6207969074911^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901626453 10000000000 6207969074911 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30854639/62500000 : ℝ)^5011 ≤ (20590899698549/50000000000000 : ℝ)^3987 := by
    have hnat : (30854639 : ℕ)^5011*50000000000000^3987 ≤ 20590899698549^3987*62500000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30854639 62500000 20590899698549 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2714263627/5000000000 : ℝ), (-1901626453/10000000000 : ℝ), (30854639/62500000 : ℝ)] ![(23201131219733/50000000000000 : ℝ), (6207969074911/50000000000000 : ℝ), (20590899698549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2714263627/5000000000 : ℝ)|^5011 ≤ (23201131219733/50000000000000 : ℝ)^3987
        have hw : |(2714263627/5000000000 : ℝ)|=(2714263627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1901626453/10000000000 : ℝ)|^5011 ≤ (6207969074911/50000000000000 : ℝ)^3987
        have hw : |(-1901626453/10000000000 : ℝ)|=(1901626453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(30854639/62500000 : ℝ)|^5011 ≤ (20590899698549/50000000000000 : ℝ)^3987
        have hw : |(30854639/62500000 : ℝ)|=(30854639/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_2 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (678566233/1250000000 : ℝ)*x 0 + (4936740713/10000000000 : ℝ)*x 1 + (-950812493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678566233/1250000000 : ℝ)^5011 ≤ (23201145239663/50000000000000 : ℝ)^3987 := by
    have hnat : (678566233 : ℕ)^5011*50000000000000^3987 ≤ 23201145239663^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678566233 1250000000 23201145239663 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4936740713/10000000000 : ℝ)^5011 ≤ (514772292343/1250000000000 : ℝ)^3987 := by
    have hnat : (4936740713 : ℕ)^5011*1250000000000^3987 ≤ 514772292343^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936740713 10000000000 514772292343 1250000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (950812493/5000000000 : ℝ)^5011 ≤ (6207963055797/50000000000000 : ℝ)^3987 := by
    have hnat : (950812493 : ℕ)^5011*50000000000000^3987 ≤ 6207963055797^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      950812493 5000000000 6207963055797 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(678566233/1250000000 : ℝ), (4936740713/10000000000 : ℝ), (-950812493/5000000000 : ℝ)] ![(23201145239663/50000000000000 : ℝ), (514772292343/1250000000000 : ℝ), (6207963055797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(678566233/1250000000 : ℝ)|^5011 ≤ (23201145239663/50000000000000 : ℝ)^3987
        have hw : |(678566233/1250000000 : ℝ)|=(678566233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4936740713/10000000000 : ℝ)|^5011 ≤ (514772292343/1250000000000 : ℝ)^3987
        have hw : |(4936740713/10000000000 : ℝ)|=(4936740713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-950812493/5000000000 : ℝ)|^5011 ≤ (6207963055797/50000000000000 : ℝ)^3987
        have hw : |(-950812493/5000000000 : ℝ)|=(950812493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_3 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4079979359/10000000000 : ℝ)*x 0 + (154440151/500000000 : ℝ)*x 1 + (2637009173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4079979359/10000000000 : ℝ)^5011 ≤ (1296347420307/4000000000000 : ℝ)^3987 := by
    have hnat : (4079979359 : ℕ)^5011*4000000000000^3987 ≤ 1296347420307^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4079979359 10000000000 1296347420307 4000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154440151/500000000 : ℝ)^5011 ≤ (22842867948791/100000000000000 : ℝ)^3987 := by
    have hnat : (154440151 : ℕ)^5011*100000000000000^3987 ≤ 22842867948791^3987*500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154440151 500000000 22842867948791 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637009173/5000000000 : ℝ)^5011 ≤ (1789937861171/4000000000000 : ℝ)^3987 := by
    have hnat : (2637009173 : ℕ)^5011*4000000000000^3987 ≤ 1789937861171^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637009173 5000000000 1789937861171 4000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4079979359/10000000000 : ℝ), (154440151/500000000 : ℝ), (2637009173/5000000000 : ℝ)] ![(1296347420307/4000000000000 : ℝ), (22842867948791/100000000000000 : ℝ), (1789937861171/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4079979359/10000000000 : ℝ)|^5011 ≤ (1296347420307/4000000000000 : ℝ)^3987
        have hw : |(4079979359/10000000000 : ℝ)|=(4079979359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(154440151/500000000 : ℝ)|^5011 ≤ (22842867948791/100000000000000 : ℝ)^3987
        have hw : |(154440151/500000000 : ℝ)|=(154440151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637009173/5000000000 : ℝ)|^5011 ≤ (1789937861171/4000000000000 : ℝ)^3987
        have hw : |(2637009173/5000000000 : ℝ)|=(2637009173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_4 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18189867/125000000 : ℝ)*x 0 + (4956843727/10000000000 : ℝ)*x 1 + (2868368557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18189867/125000000 : ℝ)^5011 ≤ (8870093208763/100000000000000 : ℝ)^3987 := by
    have hnat : (18189867 : ℕ)^5011*100000000000000^3987 ≤ 8870093208763^3987*125000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18189867 125000000 8870093208763 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4956843727/10000000000 : ℝ)^5011 ≤ (8278532250147/20000000000000 : ℝ)^3987 := by
    have hnat : (4956843727 : ℕ)^5011*20000000000000^3987 ≤ 8278532250147^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4956843727 10000000000 8278532250147 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2868368557/5000000000 : ℝ)^5011 ≤ (49737245534291/100000000000000 : ℝ)^3987 := by
    have hnat : (2868368557 : ℕ)^5011*100000000000000^3987 ≤ 49737245534291^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2868368557 5000000000 49737245534291 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18189867/125000000 : ℝ), (4956843727/10000000000 : ℝ), (2868368557/5000000000 : ℝ)] ![(8870093208763/100000000000000 : ℝ), (8278532250147/20000000000000 : ℝ), (49737245534291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18189867/125000000 : ℝ)|^5011 ≤ (8870093208763/100000000000000 : ℝ)^3987
        have hw : |(-18189867/125000000 : ℝ)|=(18189867/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4956843727/10000000000 : ℝ)|^5011 ≤ (8278532250147/20000000000000 : ℝ)^3987
        have hw : |(4956843727/10000000000 : ℝ)|=(4956843727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2868368557/5000000000 : ℝ)|^5011 ≤ (49737245534291/100000000000000 : ℝ)^3987
        have hw : |(2868368557/5000000000 : ℝ)|=(2868368557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_5 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301188243/2500000000 : ℝ)*x 0 + (-137703851/1250000000 : ℝ)*x 1 + (1147347439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301188243/2500000000 : ℝ)^5011 ≤ (8802211999629/20000000000000 : ℝ)^3987 := by
    have hnat : (1301188243 : ℕ)^5011*20000000000000^3987 ≤ 8802211999629^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301188243 2500000000 8802211999629 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137703851/1250000000 : ℝ)^5011 ≤ (1250338713971/20000000000000 : ℝ)^3987 := by
    have hnat : (137703851 : ℕ)^5011*20000000000000^3987 ≤ 1250338713971^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137703851 1250000000 1250338713971 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147347439/2000000000 : ℝ)^5011 ≤ (12434311604231/25000000000000 : ℝ)^3987 := by
    have hnat : (1147347439 : ℕ)^5011*25000000000000^3987 ≤ 12434311604231^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147347439 2000000000 12434311604231 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301188243/2500000000 : ℝ), (-137703851/1250000000 : ℝ), (1147347439/2000000000 : ℝ)] ![(8802211999629/20000000000000 : ℝ), (1250338713971/20000000000000 : ℝ), (12434311604231/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301188243/2500000000 : ℝ)|^5011 ≤ (8802211999629/20000000000000 : ℝ)^3987
        have hw : |(1301188243/2500000000 : ℝ)|=(1301188243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137703851/1250000000 : ℝ)|^5011 ≤ (1250338713971/20000000000000 : ℝ)^3987
        have hw : |(-137703851/1250000000 : ℝ)|=(137703851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147347439/2000000000 : ℝ)|^5011 ≤ (12434311604231/25000000000000 : ℝ)^3987
        have hw : |(1147347439/2000000000 : ℝ)|=(1147347439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_6 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301188243/2500000000 : ℝ)*x 0 + (1434184287/2500000000 : ℝ)*x 1 + (-550815439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301188243/2500000000 : ℝ)^5011 ≤ (8802211999629/20000000000000 : ℝ)^3987 := by
    have hnat : (1301188243 : ℕ)^5011*20000000000000^3987 ≤ 8802211999629^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301188243 2500000000 8802211999629 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1434184287/2500000000 : ℝ)^5011 ≤ (49737245904779/100000000000000 : ℝ)^3987 := by
    have hnat : (1434184287 : ℕ)^5011*100000000000000^3987 ≤ 49737245904779^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434184287 2500000000 49737245904779 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550815439/5000000000 : ℝ)^5011 ≤ (6251694069127/100000000000000 : ℝ)^3987 := by
    have hnat : (550815439 : ℕ)^5011*100000000000000^3987 ≤ 6251694069127^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550815439 5000000000 6251694069127 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301188243/2500000000 : ℝ), (1434184287/2500000000 : ℝ), (-550815439/5000000000 : ℝ)] ![(8802211999629/20000000000000 : ℝ), (49737245904779/100000000000000 : ℝ), (6251694069127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301188243/2500000000 : ℝ)|^5011 ≤ (8802211999629/20000000000000 : ℝ)^3987
        have hw : |(1301188243/2500000000 : ℝ)|=(1301188243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1434184287/2500000000 : ℝ)|^5011 ≤ (49737245904779/100000000000000 : ℝ)^3987
        have hw : |(1434184287/2500000000 : ℝ)|=(1434184287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550815439/5000000000 : ℝ)|^5011 ≤ (6251694069127/100000000000000 : ℝ)^3987
        have hw : |(-550815439/5000000000 : ℝ)|=(550815439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s0_7 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1021359567/2500000000 : ℝ)*x 0 + (261024809/500000000 : ℝ)*x 1 + (786034371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021359567/2500000000 : ℝ)^5011 ≤ (649263874707/2000000000000 : ℝ)^3987 := by
    have hnat : (1021359567 : ℕ)^5011*2000000000000^3987 ≤ 649263874707^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021359567 2500000000 649263874707 2000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261024809/500000000 : ℝ)^5011 ≤ (8835687851583/20000000000000 : ℝ)^3987 := by
    have hnat : (261024809 : ℕ)^5011*20000000000000^3987 ≤ 8835687851583^3987*500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261024809 500000000 8835687851583 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (786034371/2500000000 : ℝ)^5011 ≤ (11679183496281/50000000000000 : ℝ)^3987 := by
    have hnat : (786034371 : ℕ)^5011*50000000000000^3987 ≤ 11679183496281^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786034371 2500000000 11679183496281 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1021359567/2500000000 : ℝ), (261024809/500000000 : ℝ), (786034371/2500000000 : ℝ)] ![(649263874707/2000000000000 : ℝ), (8835687851583/20000000000000 : ℝ), (11679183496281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1021359567/2500000000 : ℝ)|^5011 ≤ (649263874707/2000000000000 : ℝ)^3987
        have hw : |(1021359567/2500000000 : ℝ)|=(1021359567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261024809/500000000 : ℝ)|^5011 ≤ (8835687851583/20000000000000 : ℝ)^3987
        have hw : |(261024809/500000000 : ℝ)|=(261024809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(786034371/2500000000 : ℝ)|^5011 ≤ (11679183496281/50000000000000 : ℝ)^3987
        have hw : |(786034371/2500000000 : ℝ)|=(786034371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1673_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (211/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22879/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5007/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5007 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5007*1^1024 ≤ 0^1024*1^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5007/1024 : ℝ) ≤ (1132956559956368827/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5007 ≤ (1132956559956368827/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5007*100000000000000000000^1024 ≤ 1132956559956368827^1024*5^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1132956559956368827 100000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1132956559956368827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5007 := by
      have hnat : (1 : ℕ)^1024*1^5007 ≤ 1^5007*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101132956559956368827/100000000000000000000 : ℝ) ≤ (626441675111001/625000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (101132956559956368827/100000000000000000000 : ℝ)^1024 ≤ (626441675111001/625000000000000 : ℝ)^5007 := by
      have hnat : (101132956559956368827 : ℕ)^1024*625000000000000^5007 ≤ 626441675111001^5007*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101132956559956368827 100000000000000000000 626441675111001 625000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626441675111001/625000000000000 : ℝ)) (X := (101132956559956368827/100000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51132956559956368827/50000000000000000000 : ℝ) ≤ (313941675111001/312500000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (51132956559956368827/50000000000000000000 : ℝ)^1024 ≤ (313941675111001/312500000000000 : ℝ)^5007 := by
      have hnat : (51132956559956368827 : ℕ)^1024*312500000000000^5007 ≤ 313941675111001^5007*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51132956559956368827 50000000000000000000 313941675111001 312500000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313941675111001/312500000000000 : ℝ)) (X := (51132956559956368827/50000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1441675111001/250000000000000 : ℝ)*(0 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1441675111001/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1132956559956368827/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1441675111001/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5007/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1441675111001/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(626441675111001/625000000000000 : ℝ) by norm_num, show 1+(1132956559956368827/100000000000000000000 : ℝ)+(0 : ℝ)=(101132956559956368827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1132956559956368827/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1441675111001/250000000000000 : ℝ)*(2/5 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1441675111001/250000000000000 : ℝ)*(2/5 : ℝ)=(313941675111001/312500000000000 : ℝ) by norm_num, show 1+2*(1132956559956368827/100000000000000000000 : ℝ)=(51132956559956368827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1441675111001/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1441675111001/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1441675111001/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1441675111001/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1441675111001/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1441675111001/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-726569281/5000000000 : ℝ)*X 0 0+(5757521083/10000000000 : ℝ)*X 0 1+(2468370561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2714263627/5000000000 : ℝ)*X 1 0+(-1901626453/10000000000 : ℝ)*X 1 1+(30854639/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((678566233/1250000000 : ℝ)*X 2 0+(4936740713/10000000000 : ℝ)*X 2 1+(-950812493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4079979359/10000000000 : ℝ)*X 0 0+(154440151/500000000 : ℝ)*X 0 1+(2637009173/5000000000 : ℝ)*X 0 2+(4079979359/10000000000 : ℝ)*X 1 0+(154440151/500000000 : ℝ)*X 1 1+(2637009173/5000000000 : ℝ)*X 1 2+(4079979359/10000000000 : ℝ)*X 2 0+(154440151/500000000 : ℝ)*X 2 1+(2637009173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18189867/125000000 : ℝ)*X 0 0+(4956843727/10000000000 : ℝ)*X 0 1+(2868368557/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1301188243/2500000000 : ℝ)*X 1 0+(-137703851/1250000000 : ℝ)*X 1 1+(1147347439/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1301188243/2500000000 : ℝ)*X 2 0+(1434184287/2500000000 : ℝ)*X 2 1+(-550815439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1021359567/2500000000 : ℝ)*X 0 0+(261024809/500000000 : ℝ)*X 0 1+(786034371/2500000000 : ℝ)*X 0 2+(1021359567/2500000000 : ℝ)*X 1 0+(261024809/500000000 : ℝ)*X 1 1+(786034371/2500000000 : ℝ)*X 1 2+(1021359567/2500000000 : ℝ)*X 2 0+(261024809/500000000 : ℝ)*X 2 1+(786034371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9057985862664948433887/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25672771/25000000000000 : ℝ)*(base1) + (156425689/50000000000000 : ℝ)*(base19) + (708895489/100000000000000 : ℝ)*(base23) + (189733819/100000000000000 : ℝ)*(base24) + (3534961/10000000000000 : ℝ)*(upper5) + (26187199803203/3125000000000 : ℝ)*(major0) + (26187199803203/3125000000000 : ℝ)*(major1) + (26187199803203/3125000000000 : ℝ)*(major2) + (609177416672957/50000000000000 : ℝ)*(sp0) + (1218357466833563/100000000000000 : ℝ)*(sp1) + (76147305065977/6250000000000 : ℝ)*(sp2) + (457621629294067/100000000000000 : ℝ)*(sp3) + (3049030111/100000000000000 : ℝ)*(sp4) + (1179116377/100000000000000 : ℝ)*(sp7) + (457622911101529/100000000000000 : ℝ)*(f.failure) + (1218357779684941/100000000000000 : ℝ)*(f.sum) + (787031873999/3125000000000000000000000000 : ℝ)*base65 + (17973425222937/3125000000000000000000000000 : ℝ)*base67 + (1336657429039/390625000000000000000000000 : ℝ)*base69 + (8608071060437/3125000000000000000000000000 : ℝ)*base71 + (7613729686499/3125000000000000000000000000 : ℝ)*base73 + (6065245406781/1562500000000000000000000000 : ℝ)*base75 + (20076920916687/3125000000000000000000000000 : ℝ)*base77 + (7242592979953/781250000000000000000000000 : ℝ)*base79 + (6304271620813/1562500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (30879487/10000000000000000000000 : ℝ)*base89 + (30879487/10000000000000000000000 : ℝ)*base91 + (30879487/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42590663262062367736827/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1431308961/100000000000000 : ℝ)*(base19) + (1436914429/100000000000000 : ℝ)*(base23) + (33183393/50000000000000 : ℝ)*(base32) + (29944111/12500000000000 : ℝ)*(upper3) + (92404917/50000000000000 : ℝ)*(upper5) + (440959630209109/50000000000000 : ℝ)*(major0) + (440959630209109/50000000000000 : ℝ)*(major1) + (440959630209109/50000000000000 : ℝ)*(major2) + (595375267/12500000000000 : ℝ)*(sp1) + (4893322323/100000000000000 : ℝ)*(sp2) + (641113009719081/50000000000000 : ℝ)*(sp4) + (256443965025413/20000000000000 : ℝ)*(sp5) + (128221968920141/10000000000000 : ℝ)*(sp6) + (481612207881281/100000000000000 : ℝ)*(sp7) + (481612274248067/100000000000000 : ℝ)*(f.failure) + (641113009719081/50000000000000 : ℝ)*(f.sum) + (10856489866891/6250000000000000000000000000 : ℝ)*base66 + (6971038116891/12500000000000000000000000000 : ℝ)*base68 + (62288147908109/12500000000000000000000000000 : ℝ)*base69 + (5005371591891/12500000000000000000000000000 : ℝ)*base72 + (1133861516891/6250000000000000000000000000 : ℝ)*base74 + (12103612320609/12500000000000000000000000000 : ℝ)*base75 + (25190907441891/12500000000000000000000000000 : ℝ)*base78 + (72870146820609/12500000000000000000000000000 : ℝ)*base79 + (18202062895609/6250000000000000000000000000 : ℝ)*base81 + (19543099/10000000000000000000000 : ℝ)*base90 + (19543099/10000000000000000000000 : ℝ)*base92 + (19543099/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1673_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (211/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22879/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1673_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1673_s1_0 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-309971081/2000000000 : ℝ)*x 0 + (68500561/125000000 : ℝ)*x 1 + (2575582749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309971081/2000000000 : ℝ)^5011 ≤ (9601295816267/100000000000000 : ℝ)^3987 := by
    have hnat : (309971081 : ℕ)^5011*100000000000000^3987 ≤ 9601295816267^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309971081 2000000000 9601295816267 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68500561/125000000 : ℝ)^5011 ≤ (46956401620029/100000000000000 : ℝ)^3987 := by
    have hnat : (68500561 : ℕ)^5011*100000000000000^3987 ≤ 46956401620029^3987*125000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68500561 125000000 46956401620029 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2575582749/5000000000 : ℝ)^5011 ≤ (43442302551293/100000000000000 : ℝ)^3987 := by
    have hnat : (2575582749 : ℕ)^5011*100000000000000^3987 ≤ 43442302551293^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575582749 5000000000 43442302551293 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-309971081/2000000000 : ℝ), (68500561/125000000 : ℝ), (2575582749/5000000000 : ℝ)] ![(9601295816267/100000000000000 : ℝ), (46956401620029/100000000000000 : ℝ), (43442302551293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-309971081/2000000000 : ℝ)|^5011 ≤ (9601295816267/100000000000000 : ℝ)^3987
        have hw : |(-309971081/2000000000 : ℝ)|=(309971081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68500561/125000000 : ℝ)|^5011 ≤ (46956401620029/100000000000000 : ℝ)^3987
        have hw : |(68500561/125000000 : ℝ)|=(68500561/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2575582749/5000000000 : ℝ)|^5011 ≤ (43442302551293/100000000000000 : ℝ)^3987
        have hw : |(2575582749/5000000000 : ℝ)|=(2575582749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_1 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354707701/10000000000 : ℝ)*x 0 + (-86017917/500000000 : ℝ)*x 1 + (5151165561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354707701/10000000000 : ℝ)^5011 ≤ (356332740789/781250000000 : ℝ)^3987 := by
    have hnat : (5354707701 : ℕ)^5011*781250000000^3987 ≤ 356332740789^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354707701 10000000000 356332740789 781250000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86017917/500000000 : ℝ)^5011 ≤ (10947105948359/100000000000000 : ℝ)^3987 := by
    have hnat : (86017917 : ℕ)^5011*100000000000000^3987 ≤ 10947105948359^3987*500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86017917 500000000 10947105948359 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151165561/10000000000 : ℝ)^5011 ≤ (43442303219061/100000000000000 : ℝ)^3987 := by
    have hnat : (5151165561 : ℕ)^5011*100000000000000^3987 ≤ 43442303219061^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151165561 10000000000 43442303219061 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354707701/10000000000 : ℝ), (-86017917/500000000 : ℝ), (5151165561/10000000000 : ℝ)] ![(356332740789/781250000000 : ℝ), (10947105948359/100000000000000 : ℝ), (43442303219061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354707701/10000000000 : ℝ)|^5011 ≤ (356332740789/781250000000 : ℝ)^3987
        have hw : |(5354707701/10000000000 : ℝ)|=(5354707701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86017917/500000000 : ℝ)|^5011 ≤ (10947105948359/100000000000000 : ℝ)^3987
        have hw : |(-86017917/500000000 : ℝ)|=(86017917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151165561/10000000000 : ℝ)|^5011 ≤ (43442303219061/100000000000000 : ℝ)^3987
        have hw : |(5151165561/10000000000 : ℝ)|=(5151165561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_2 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677353821/5000000000 : ℝ)*x 0 + (2575582847/5000000000 : ℝ)*x 1 + (-860179121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677353821/5000000000 : ℝ)^5011 ≤ (22805295094683/50000000000000 : ℝ)^3987 := by
    have hnat : (2677353821 : ℕ)^5011*50000000000000^3987 ≤ 22805295094683^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677353821 5000000000 22805295094683 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575582847/5000000000 : ℝ)^5011 ≤ (8688460925759/20000000000000 : ℝ)^3987 := by
    have hnat : (2575582847 : ℕ)^5011*20000000000000^3987 ≤ 8688460925759^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575582847 5000000000 8688460925759 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860179121/5000000000 : ℝ)^5011 ≤ (2736776291149/25000000000000 : ℝ)^3987 := by
    have hnat : (860179121 : ℕ)^5011*25000000000000^3987 ≤ 2736776291149^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860179121 5000000000 2736776291149 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677353821/5000000000 : ℝ), (2575582847/5000000000 : ℝ), (-860179121/5000000000 : ℝ)] ![(22805295094683/50000000000000 : ℝ), (8688460925759/20000000000000 : ℝ), (2736776291149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677353821/5000000000 : ℝ)|^5011 ≤ (22805295094683/50000000000000 : ℝ)^3987
        have hw : |(2677353821/5000000000 : ℝ)|=(2677353821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575582847/5000000000 : ℝ)|^5011 ≤ (8688460925759/20000000000000 : ℝ)^3987
        have hw : |(2575582847/5000000000 : ℝ)|=(2575582847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-860179121/5000000000 : ℝ)|^5011 ≤ (2736776291149/25000000000000 : ℝ)^3987
        have hw : |(-860179121/5000000000 : ℝ)|=(860179121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_3 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039407627/2500000000 : ℝ)*x 0 + (747194821/2000000000 : ℝ)*x 1 + (4611569987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039407627/2500000000 : ℝ)^5011 ≤ (3318579945539/10000000000000 : ℝ)^3987 := by
    have hnat : (1039407627 : ℕ)^5011*10000000000000^3987 ≤ 3318579945539^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039407627 2500000000 3318579945539 10000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (747194821/2000000000 : ℝ)^5011 ≤ (1450615551981/5000000000000 : ℝ)^3987 := by
    have hnat : (747194821 : ℕ)^5011*5000000000000^3987 ≤ 1450615551981^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      747194821 2000000000 1450615551981 5000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4611569987/10000000000 : ℝ)^5011 ≤ (18900944745569/50000000000000 : ℝ)^3987 := by
    have hnat : (4611569987 : ℕ)^5011*50000000000000^3987 ≤ 18900944745569^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4611569987 10000000000 18900944745569 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039407627/2500000000 : ℝ), (747194821/2000000000 : ℝ), (4611569987/10000000000 : ℝ)] ![(3318579945539/10000000000000 : ℝ), (1450615551981/5000000000000 : ℝ), (18900944745569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039407627/2500000000 : ℝ)|^5011 ≤ (3318579945539/10000000000000 : ℝ)^3987
        have hw : |(1039407627/2500000000 : ℝ)|=(1039407627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(747194821/2000000000 : ℝ)|^5011 ≤ (1450615551981/5000000000000 : ℝ)^3987
        have hw : |(747194821/2000000000 : ℝ)|=(747194821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4611569987/10000000000 : ℝ)|^5011 ≤ (18900944745569/50000000000000 : ℝ)^3987
        have hw : |(4611569987/10000000000 : ℝ)|=(4611569987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_4 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1549985957/10000000000 : ℝ)*x 0 + (2577195353/5000000000 : ℝ)*x 1 + (136919391/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1549985957/10000000000 : ℝ)^5011 ≤ (1920462462167/20000000000000 : ℝ)^3987 := by
    have hnat : (1549985957 : ℕ)^5011*20000000000000^3987 ≤ 1920462462167^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549985957 10000000000 1920462462167 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577195353/5000000000 : ℝ)^5011 ≤ (108691227253/250000000000 : ℝ)^3987 := by
    have hnat : (2577195353 : ℕ)^5011*250000000000^3987 ≤ 108691227253^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577195353 5000000000 108691227253 250000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136919391/250000000 : ℝ)^5011 ≤ (9384239355813/20000000000000 : ℝ)^3987 := by
    have hnat : (136919391 : ℕ)^5011*20000000000000^3987 ≤ 9384239355813^3987*250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136919391 250000000 9384239355813 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1549985957/10000000000 : ℝ), (2577195353/5000000000 : ℝ), (136919391/250000000 : ℝ)] ![(1920462462167/20000000000000 : ℝ), (108691227253/250000000000 : ℝ), (9384239355813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1549985957/10000000000 : ℝ)|^5011 ≤ (1920462462167/20000000000000 : ℝ)^3987
        have hw : |(-1549985957/10000000000 : ℝ)|=(1549985957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577195353/5000000000 : ℝ)|^5011 ≤ (108691227253/250000000000 : ℝ)^3987
        have hw : |(2577195353/5000000000 : ℝ)|=(2577195353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136919391/250000000 : ℝ)|^5011 ≤ (9384239355813/20000000000000 : ℝ)^3987
        have hw : |(136919391/250000000 : ℝ)|=(136919391/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_5 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053318197/2000000000 : ℝ)*x 0 + (-27894961/200000000 : ℝ)*x 1 + (684596957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053318197/2000000000 : ℝ)^5011 ≤ (44669256509653/100000000000000 : ℝ)^3987 := by
    have hnat : (1053318197 : ℕ)^5011*100000000000000^3987 ≤ 44669256509653^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053318197 2000000000 44669256509653 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27894961/200000000 : ℝ)^5011 ≤ (8409546529633/100000000000000 : ℝ)^3987 := by
    have hnat : (27894961 : ℕ)^5011*100000000000000^3987 ≤ 8409546529633^3987*200000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27894961 200000000 8409546529633 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684596957/1250000000 : ℝ)^5011 ≤ (11730299237837/25000000000000 : ℝ)^3987 := by
    have hnat : (684596957 : ℕ)^5011*25000000000000^3987 ≤ 11730299237837^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684596957 1250000000 11730299237837 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053318197/2000000000 : ℝ), (-27894961/200000000 : ℝ), (684596957/1250000000 : ℝ)] ![(44669256509653/100000000000000 : ℝ), (8409546529633/100000000000000 : ℝ), (11730299237837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053318197/2000000000 : ℝ)|^5011 ≤ (44669256509653/100000000000000 : ℝ)^3987
        have hw : |(1053318197/2000000000 : ℝ)|=(1053318197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27894961/200000000 : ℝ)|^5011 ≤ (8409546529633/100000000000000 : ℝ)^3987
        have hw : |(-27894961/200000000 : ℝ)|=(27894961/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684596957/1250000000 : ℝ)|^5011 ≤ (11730299237837/25000000000000 : ℝ)^3987
        have hw : |(684596957/1250000000 : ℝ)|=(684596957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_6 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266590939/10000000000 : ℝ)*x 0 + (5476775621/10000000000 : ℝ)*x 1 + (-278949633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266590939/10000000000 : ℝ)^5011 ≤ (44669256019293/100000000000000 : ℝ)^3987 := by
    have hnat : (5266590939 : ℕ)^5011*100000000000000^3987 ≤ 44669256019293^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266590939 10000000000 44669256019293 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476775621/10000000000 : ℝ)^5011 ≤ (46921196574479/100000000000000 : ℝ)^3987 := by
    have hnat : (5476775621 : ℕ)^5011*100000000000000^3987 ≤ 46921196574479^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476775621 10000000000 46921196574479 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278949633/2000000000 : ℝ)^5011 ≤ (525596712569/6250000000000 : ℝ)^3987 := by
    have hnat : (278949633 : ℕ)^5011*6250000000000^3987 ≤ 525596712569^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278949633 2000000000 525596712569 6250000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266590939/10000000000 : ℝ), (5476775621/10000000000 : ℝ), (-278949633/2000000000 : ℝ)] ![(44669256019293/100000000000000 : ℝ), (46921196574479/100000000000000 : ℝ), (525596712569/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266590939/10000000000 : ℝ)|^5011 ≤ (44669256019293/100000000000000 : ℝ)^3987
        have hw : |(5266590939/10000000000 : ℝ)|=(5266590939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476775621/10000000000 : ℝ)|^5011 ≤ (46921196574479/100000000000000 : ℝ)^3987
        have hw : |(5476775621/10000000000 : ℝ)|=(5476775621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278949633/2000000000 : ℝ)|^5011 ≤ (525596712569/6250000000000 : ℝ)^3987
        have hw : |(-278949633/2000000000 : ℝ)|=(278949633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s1_7 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (831595371/2000000000 : ℝ)*x 0 + (2301491369/5000000000 : ℝ)*x 1 + (748935553/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (831595371/2000000000 : ℝ)^5011 ≤ (829731850549/2500000000000 : ℝ)^3987 := by
    have hnat : (831595371 : ℕ)^5011*2500000000000^3987 ≤ 829731850549^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831595371 2000000000 829731850549 2500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2301491369/5000000000 : ℝ)^5011 ≤ (37713440473187/100000000000000 : ℝ)^3987 := by
    have hnat : (2301491369 : ℕ)^5011*100000000000000^3987 ≤ 37713440473187^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301491369 5000000000 37713440473187 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748935553/2000000000 : ℝ)^5011 ≤ (29097285494391/100000000000000 : ℝ)^3987 := by
    have hnat : (748935553 : ℕ)^5011*100000000000000^3987 ≤ 29097285494391^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748935553 2000000000 29097285494391 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(831595371/2000000000 : ℝ), (2301491369/5000000000 : ℝ), (748935553/2000000000 : ℝ)] ![(829731850549/2500000000000 : ℝ), (37713440473187/100000000000000 : ℝ), (29097285494391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(831595371/2000000000 : ℝ)|^5011 ≤ (829731850549/2500000000000 : ℝ)^3987
        have hw : |(831595371/2000000000 : ℝ)|=(831595371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2301491369/5000000000 : ℝ)|^5011 ≤ (37713440473187/100000000000000 : ℝ)^3987
        have hw : |(2301491369/5000000000 : ℝ)|=(2301491369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748935553/2000000000 : ℝ)|^5011 ≤ (29097285494391/100000000000000 : ℝ)^3987
        have hw : |(748935553/2000000000 : ℝ)|=(748935553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1673_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5023/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3409/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (211/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (211/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (211/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (211/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (211/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (211/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (211/4000 : ℝ) ^ (5007/1024 : ℝ) ≤ (28254463926113/50000000000000000000 : ℝ) := by
    have hpowers : (211/4000 : ℝ)^5007 ≤ (28254463926113/50000000000000000000 : ℝ)^1024 := by
      have hnat : (211 : ℕ)^5007*50000000000000000000^1024 ≤ 28254463926113^1024*4000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        211 4000 28254463926113 50000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (211/4000 : ℝ)) (X := (28254463926113/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22879/100000 : ℝ) ^ (5007/1024 : ℝ) ≤ (73768731443686983/100000000000000000000 : ℝ) := by
    have hpowers : (22879/100000 : ℝ)^5007 ≤ (73768731443686983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22879 : ℕ)^5007*100000000000000000000^1024 ≤ 73768731443686983^1024*100000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22879 100000 73768731443686983 100000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22879/100000 : ℝ)) (X := (73768731443686983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000028254463926113/25000000000000000000 : ℝ) ≤ (10000002311368729/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (25000028254463926113/25000000000000000000 : ℝ)^1024 ≤ (10000002311368729/10000000000000000 : ℝ)^5007 := by
      have hnat : (25000028254463926113 : ℕ)^1024*10000000000000000^5007 ≤ 10000002311368729^5007*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000028254463926113 25000000000000000000 10000002311368729 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002311368729/10000000000000000 : ℝ)) (X := (25000028254463926113/25000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100073825240371539209/100000000000000000000 : ℝ) ≤ (10001509384022699/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (100073825240371539209/100000000000000000000 : ℝ)^1024 ≤ (10001509384022699/10000000000000000 : ℝ)^5007 := by
      have hnat : (100073825240371539209 : ℕ)^1024*10000000000000000^5007 ≤ 10001509384022699^5007*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100073825240371539209 100000000000000000000 10001509384022699 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001509384022699/10000000000000000 : ℝ)) (X := (100073825240371539209/100000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073768731443686983/50000000000000000000 : ℝ) ≤ (10003016456676669/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (50073768731443686983/50000000000000000000 : ℝ)^1024 ≤ (10003016456676669/10000000000000000 : ℝ)^5007 := by
      have hnat : (50073768731443686983 : ℕ)^1024*10000000000000000^5007 ≤ 10003016456676669^5007*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073768731443686983 50000000000000000000 10003016456676669 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003016456676669/10000000000000000 : ℝ)) (X := (50073768731443686983/50000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(28254463926113/50000000000000000000 : ℝ) ≤ ((22003017634104465227/22005000000000000000 : ℝ)+2*(150707265397/176040000000000 : ℝ)*(211/4000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (22003017634104465227/22005000000000000000 : ℝ)+2*(150707265397/176040000000000 : ℝ)*(211/4000 : ℝ)=(10000002311368729/10000000000000000 : ℝ) by norm_num, show 1+2*(28254463926113/50000000000000000000 : ℝ)=(25000028254463926113/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73768731443686983/100000000000000000000 : ℝ)+(28254463926113/50000000000000000000 : ℝ) ≤ ((22003017634104465227/22005000000000000000 : ℝ)+(150707265397/176040000000000 : ℝ)*((22879/100000 : ℝ)+(211/4000 : ℝ)))^(5007/1024 : ℝ) := by
    rw [show (22003017634104465227/22005000000000000000 : ℝ)+(150707265397/176040000000000 : ℝ)*((22879/100000 : ℝ)+(211/4000 : ℝ))=(10001509384022699/10000000000000000 : ℝ) by norm_num, show 1+(73768731443686983/100000000000000000000 : ℝ)+(28254463926113/50000000000000000000 : ℝ)=(100073825240371539209/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73768731443686983/100000000000000000000 : ℝ) ≤ ((22003017634104465227/22005000000000000000 : ℝ)+2*(150707265397/176040000000000 : ℝ)*(22879/100000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (22003017634104465227/22005000000000000000 : ℝ)+2*(150707265397/176040000000000 : ℝ)*(22879/100000 : ℝ)=(10003016456676669/10000000000000000 : ℝ) by norm_num, show 1+2*(73768731443686983/100000000000000000000 : ℝ)=(50073768731443686983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22003017634104465227/22005000000000000000 : ℝ)*(X 1 0+X 2 0)+(150707265397/176040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (211/4000 : ℝ)) (hi := (22879/100000 : ℝ)) (c := (22003017634104465227/22005000000000000000 : ℝ)) (alpha := (150707265397/176040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22003017634104465227/22005000000000000000 : ℝ)*(X 0 1+X 2 1)+(150707265397/176040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (211/4000 : ℝ)) (hi := (22879/100000 : ℝ)) (c := (22003017634104465227/22005000000000000000 : ℝ)) (alpha := (150707265397/176040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22003017634104465227/22005000000000000000 : ℝ)*(X 0 2+X 1 2)+(150707265397/176040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (211/4000 : ℝ)) (hi := (22879/100000 : ℝ)) (c := (22003017634104465227/22005000000000000000 : ℝ)) (alpha := (150707265397/176040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-309971081/2000000000 : ℝ)*X 0 0+(68500561/125000000 : ℝ)*X 0 1+(2575582749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354707701/10000000000 : ℝ)*X 1 0+(-86017917/500000000 : ℝ)*X 1 1+(5151165561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677353821/5000000000 : ℝ)*X 2 0+(2575582847/5000000000 : ℝ)*X 2 1+(-860179121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1039407627/2500000000 : ℝ)*X 0 0+(747194821/2000000000 : ℝ)*X 0 1+(4611569987/10000000000 : ℝ)*X 0 2+(1039407627/2500000000 : ℝ)*X 1 0+(747194821/2000000000 : ℝ)*X 1 1+(4611569987/10000000000 : ℝ)*X 1 2+(1039407627/2500000000 : ℝ)*X 2 0+(747194821/2000000000 : ℝ)*X 2 1+(4611569987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1549985957/10000000000 : ℝ)*X 0 0+(2577195353/5000000000 : ℝ)*X 0 1+(136919391/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053318197/2000000000 : ℝ)*X 1 0+(-27894961/200000000 : ℝ)*X 1 1+(684596957/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266590939/10000000000 : ℝ)*X 2 0+(5476775621/10000000000 : ℝ)*X 2 1+(-278949633/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((831595371/2000000000 : ℝ)*X 0 0+(2301491369/5000000000 : ℝ)*X 0 1+(748935553/2000000000 : ℝ)*X 0 2+(831595371/2000000000 : ℝ)*X 1 0+(2301491369/5000000000 : ℝ)*X 1 1+(748935553/2000000000 : ℝ)*X 1 2+(831595371/2000000000 : ℝ)*X 2 0+(2301491369/5000000000 : ℝ)*X 2 1+(748935553/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (292128099518467701788388449/91687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (178447577/100000000000000 : ℝ)*(base19) + (4595579/50000000000000 : ℝ)*(base23) + (6062711/6250000000000 : ℝ)*(lower2) + (48125273/100000000000000 : ℝ)*(upper3) + (12155621/50000000000000 : ℝ)*(lower4) + (522839113045687/25000000000000 : ℝ)*(major0) + (522839113045687/25000000000000 : ℝ)*(major1) + (522839113045687/25000000000000 : ℝ)*(major2) + (152031518173617/5000000000000 : ℝ)*(sp0) + (1520315976345193/50000000000000 : ℝ)*(sp1) + (760158030486701/25000000000000 : ℝ)*(sp2) + (1142079734438011/100000000000000 : ℝ)*(sp3) + (1767665623/100000000000000 : ℝ)*(sp4) + (932585253/100000000000000 : ℝ)*(sp7) + (35690020844477/3125000000000 : ℝ)*(f.failure) + (1520316065568981/50000000000000 : ℝ)*(f.sum) + (1937355157843/2200500000000000000000000000 : ℝ)*base65 + (1203225656267174051/550125000000000000000000000000000 : ℝ)*base68 + (3229246655209049051/550125000000000000000000000000000 : ℝ)*base70 + (196988481810075949/550125000000000000000000000000000 : ℝ)*base71 + (7901433269249/4401000000000000000000000000 : ℝ)*base73 + (1392845514447299051/550125000000000000000000000000000 : ℝ)*base76 + (5146603164987674051/550125000000000000000000000000000 : ℝ)*base78 + (5996687699965575949/550125000000000000000000000000000 : ℝ)*base79 + (1617473075239/1100250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1232869/312500000000000000000 : ℝ)*base90 + (1232869/312500000000000000000 : ℝ)*base92 + (1232869/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (901812163866660344219594647/73350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3917007/195312500000 : ℝ)*(base19) + (2012354803/100000000000000 : ℝ)*(base23) + (281186571/100000000000000 : ℝ)*(upper3) + (5441857/20000000000000 : ℝ)*(lower4) + (156850247/50000000000000 : ℝ)*(upper5) + (426696917325461/20000000000000 : ℝ)*(major0) + (426696917325461/20000000000000 : ℝ)*(major1) + (426696917325461/20000000000000 : ℝ)*(major2) + (1211019949/6250000000000 : ℝ)*(sp1) + (1831698977/10000000000000 : ℝ)*(sp2) + (310188210532849/10000000000000 : ℝ)*(sp4) + (3101860723501723/100000000000000 : ℝ)*(sp5) + (1550930887991959/50000000000000 : ℝ)*(sp6) + (291271664526159/25000000000000 : ℝ)*(sp7) + (291271664526159/25000000000000 : ℝ)*(f.failure) + (310188210532849/10000000000000 : ℝ)*(f.sum) + (4389926636923/1760400000000000000000000000 : ℝ)*base66 + (4744386720892569647/440100000000000000000000000000000 : ℝ)*base67 + (400769233329369647/440100000000000000000000000000000 : ℝ)*base69 + (1765095239508530353/440100000000000000000000000000000 : ℝ)*base72 + (39670494697369/8802000000000000000000000000 : ℝ)*base73 + (1771077577341830353/440100000000000000000000000000000 : ℝ)*base76 + (277882122648830353/440100000000000000000000000000000 : ℝ)*base78 + (1430392106979230353/440100000000000000000000000000000 : ℝ)*base80 + (32887889549/70416000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4956377/2500000000000000000000 : ℝ)*base89 + (4956377/2500000000000000000000 : ℝ)*base91 + (4956377/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1673_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (211/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5023/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3409/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1673_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1673_s2_0 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-778599969/5000000000 : ℝ)*x 0 + (2721613419/5000000000 : ℝ)*x 1 + (5183117389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (778599969/5000000000 : ℝ)^5011 ≤ (9658515430073/100000000000000 : ℝ)^3987 := by
    have hnat : (778599969 : ℕ)^5011*100000000000000^3987 ≤ 9658515430073^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778599969 5000000000 9658515430073 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721613419/5000000000 : ℝ)^5011 ≤ (23280119242127/50000000000000 : ℝ)^3987 := by
    have hnat : (2721613419 : ℕ)^5011*50000000000000^3987 ≤ 23280119242127^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721613419 5000000000 23280119242127 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183117389/10000000000 : ℝ)^5011 ≤ (43781246072531/100000000000000 : ℝ)^3987 := by
    have hnat : (5183117389 : ℕ)^5011*100000000000000^3987 ≤ 43781246072531^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183117389 10000000000 43781246072531 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-778599969/5000000000 : ℝ), (2721613419/5000000000 : ℝ), (5183117389/10000000000 : ℝ)] ![(9658515430073/100000000000000 : ℝ), (23280119242127/50000000000000 : ℝ), (43781246072531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-778599969/5000000000 : ℝ)|^5011 ≤ (9658515430073/100000000000000 : ℝ)^3987
        have hw : |(-778599969/5000000000 : ℝ)|=(778599969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721613419/5000000000 : ℝ)|^5011 ≤ (23280119242127/50000000000000 : ℝ)^3987
        have hw : |(2721613419/5000000000 : ℝ)|=(2721613419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183117389/10000000000 : ℝ)|^5011 ≤ (43781246072531/100000000000000 : ℝ)^3987
        have hw : |(5183117389/10000000000 : ℝ)|=(5183117389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_1 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344892669/10000000000 : ℝ)*x 0 + (-845524263/5000000000 : ℝ)*x 1 + (323944837/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344892669/10000000000 : ℝ)^5011 ≤ (9101108092881/20000000000000 : ℝ)^3987 := by
    have hnat : (5344892669 : ℕ)^5011*20000000000000^3987 ≤ 9101108092881^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344892669 10000000000 9101108092881 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845524263/5000000000 : ℝ)^5011 ≤ (5356606703781/50000000000000 : ℝ)^3987 := by
    have hnat : (845524263 : ℕ)^5011*50000000000000^3987 ≤ 5356606703781^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845524263 5000000000 5356606703781 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323944837/625000000 : ℝ)^5011 ≤ (2189062305219/5000000000000 : ℝ)^3987 := by
    have hnat : (323944837 : ℕ)^5011*5000000000000^3987 ≤ 2189062305219^3987*625000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323944837 625000000 2189062305219 5000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344892669/10000000000 : ℝ), (-845524263/5000000000 : ℝ), (323944837/625000000 : ℝ)] ![(9101108092881/20000000000000 : ℝ), (5356606703781/50000000000000 : ℝ), (2189062305219/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344892669/10000000000 : ℝ)|^5011 ≤ (9101108092881/20000000000000 : ℝ)^3987
        have hw : |(5344892669/10000000000 : ℝ)|=(5344892669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-845524263/5000000000 : ℝ)|^5011 ≤ (5356606703781/50000000000000 : ℝ)^3987
        have hw : |(-845524263/5000000000 : ℝ)|=(845524263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323944837/625000000 : ℝ)|^5011 ≤ (2189062305219/5000000000000 : ℝ)^3987
        have hw : |(323944837/625000000 : ℝ)|=(323944837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_2 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534489251/1000000000 : ℝ)*x 0 + (1036623489/2000000000 : ℝ)*x 1 + (-169104867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534489251/1000000000 : ℝ)^5011 ≤ (11376384690757/25000000000000 : ℝ)^3987 := by
    have hnat : (534489251 : ℕ)^5011*25000000000000^3987 ≤ 11376384690757^3987*1000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534489251 1000000000 11376384690757 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036623489/2000000000 : ℝ)^5011 ≤ (43781246667047/100000000000000 : ℝ)^3987 := by
    have hnat : (1036623489 : ℕ)^5011*100000000000000^3987 ≤ 43781246667047^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036623489 2000000000 43781246667047 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169104867/1000000000 : ℝ)^5011 ≤ (5356607277071/50000000000000 : ℝ)^3987 := by
    have hnat : (169104867 : ℕ)^5011*50000000000000^3987 ≤ 5356607277071^3987*1000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169104867 1000000000 5356607277071 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534489251/1000000000 : ℝ), (1036623489/2000000000 : ℝ), (-169104867/1000000000 : ℝ)] ![(11376384690757/25000000000000 : ℝ), (43781246667047/100000000000000 : ℝ), (5356607277071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534489251/1000000000 : ℝ)|^5011 ≤ (11376384690757/25000000000000 : ℝ)^3987
        have hw : |(534489251/1000000000 : ℝ)|=(534489251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036623489/2000000000 : ℝ)|^5011 ≤ (43781246667047/100000000000000 : ℝ)^3987
        have hw : |(1036623489/2000000000 : ℝ)|=(1036623489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169104867/1000000000 : ℝ)|^5011 ≤ (5356607277071/50000000000000 : ℝ)^3987
        have hw : |(-169104867/1000000000 : ℝ)|=(169104867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_3 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520391757/1250000000 : ℝ)*x 0 + (1913491059/5000000000 : ℝ)*x 1 + (2259743789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520391757/1250000000 : ℝ)^5011 ≤ (33241020054509/100000000000000 : ℝ)^3987 := by
    have hnat : (520391757 : ℕ)^5011*100000000000000^3987 ≤ 33241020054509^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520391757 1250000000 33241020054509 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913491059/5000000000 : ℝ)^5011 ≤ (7475831314759/25000000000000 : ℝ)^3987 := by
    have hnat : (1913491059 : ℕ)^5011*25000000000000^3987 ≤ 7475831314759^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913491059 5000000000 7475831314759 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259743789/5000000000 : ℝ)^5011 ≤ (36855654671669/100000000000000 : ℝ)^3987 := by
    have hnat : (2259743789 : ℕ)^5011*100000000000000^3987 ≤ 36855654671669^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259743789 5000000000 36855654671669 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520391757/1250000000 : ℝ), (1913491059/5000000000 : ℝ), (2259743789/5000000000 : ℝ)] ![(33241020054509/100000000000000 : ℝ), (7475831314759/25000000000000 : ℝ), (36855654671669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520391757/1250000000 : ℝ)|^5011 ≤ (33241020054509/100000000000000 : ℝ)^3987
        have hw : |(520391757/1250000000 : ℝ)|=(520391757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1913491059/5000000000 : ℝ)|^5011 ≤ (7475831314759/25000000000000 : ℝ)^3987
        have hw : |(1913491059/5000000000 : ℝ)|=(1913491059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259743789/5000000000 : ℝ)|^5011 ≤ (36855654671669/100000000000000 : ℝ)^3987
        have hw : |(2259743789/5000000000 : ℝ)|=(2259743789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_4 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1557265203/10000000000 : ℝ)*x 0 + (162035603/312500000 : ℝ)*x 1 + (1360295669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557265203/10000000000 : ℝ)^5011 ≤ (1207378025793/12500000000000 : ℝ)^3987 := by
    have hnat : (1557265203 : ℕ)^5011*12500000000000^3987 ≤ 1207378025793^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557265203 10000000000 1207378025793 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162035603/312500000 : ℝ)^5011 ≤ (4380271242071/10000000000000 : ℝ)^3987 := by
    have hnat : (162035603 : ℕ)^5011*10000000000000^3987 ≤ 4380271242071^3987*312500000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162035603 312500000 4380271242071 10000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360295669/2500000000 : ℝ)^5011 ≤ (181790091259/390625000000 : ℝ)^3987 := by
    have hnat : (1360295669 : ℕ)^5011*390625000000^3987 ≤ 181790091259^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360295669 2500000000 181790091259 390625000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1557265203/10000000000 : ℝ), (162035603/312500000 : ℝ), (1360295669/2500000000 : ℝ)] ![(1207378025793/12500000000000 : ℝ), (4380271242071/10000000000000 : ℝ), (181790091259/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1557265203/10000000000 : ℝ)|^5011 ≤ (1207378025793/12500000000000 : ℝ)^3987
        have hw : |(-1557265203/10000000000 : ℝ)|=(1557265203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162035603/312500000 : ℝ)|^5011 ≤ (4380271242071/10000000000000 : ℝ)^3987
        have hw : |(162035603/312500000 : ℝ)|=(162035603/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360295669/2500000000 : ℝ)|^5011 ≤ (181790091259/390625000000 : ℝ)^3987
        have hw : |(1360295669/2500000000 : ℝ)|=(1360295669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_5 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275236453/10000000000 : ℝ)*x 0 + (-358245709/2500000000 : ℝ)*x 1 + (2720591191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275236453/10000000000 : ℝ)^5011 ≤ (5595179579851/12500000000000 : ℝ)^3987 := by
    have hnat : (5275236453 : ℕ)^5011*12500000000000^3987 ≤ 5595179579851^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275236453 10000000000 5595179579851 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (358245709/2500000000 : ℝ)^5011 ≤ (2175075786809/25000000000000 : ℝ)^3987 := by
    have hnat : (358245709 : ℕ)^5011*25000000000000^3987 ≤ 2175075786809^3987*2500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358245709 2500000000 2175075786809 25000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720591191/5000000000 : ℝ)^5011 ≤ (46538260201901/100000000000000 : ℝ)^3987 := by
    have hnat : (2720591191 : ℕ)^5011*100000000000000^3987 ≤ 46538260201901^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720591191 5000000000 46538260201901 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275236453/10000000000 : ℝ), (-358245709/2500000000 : ℝ), (2720591191/5000000000 : ℝ)] ![(5595179579851/12500000000000 : ℝ), (2175075786809/25000000000000 : ℝ), (46538260201901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275236453/10000000000 : ℝ)|^5011 ≤ (5595179579851/12500000000000 : ℝ)^3987
        have hw : |(5275236453/10000000000 : ℝ)|=(5275236453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-358245709/2500000000 : ℝ)|^5011 ≤ (2175075786809/25000000000000 : ℝ)^3987
        have hw : |(-358245709/2500000000 : ℝ)|=(358245709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720591191/5000000000 : ℝ)|^5011 ≤ (46538260201901/100000000000000 : ℝ)^3987
        have hw : |(2720591191/5000000000 : ℝ)|=(2720591191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_6 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275235321/10000000000 : ℝ)*x 0 + (272059159/500000000 : ℝ)*x 1 + (-716491647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275235321/10000000000 : ℝ)^5011 ≤ (44761424566601/100000000000000 : ℝ)^3987 := by
    have hnat : (5275235321 : ℕ)^5011*100000000000000^3987 ≤ 44761424566601^3987*10000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275235321 10000000000 44761424566601 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272059159/500000000 : ℝ)^5011 ≤ (5817283597517/12500000000000 : ℝ)^3987 := by
    have hnat : (272059159 : ℕ)^5011*12500000000000^3987 ≤ 5817283597517^3987*500000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272059159 500000000 5817283597517 12500000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716491647/5000000000 : ℝ)^5011 ≤ (1740061328431/20000000000000 : ℝ)^3987 := by
    have hnat : (716491647 : ℕ)^5011*20000000000000^3987 ≤ 1740061328431^3987*5000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716491647 5000000000 1740061328431 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275235321/10000000000 : ℝ), (272059159/500000000 : ℝ), (-716491647/5000000000 : ℝ)] ![(44761424566601/100000000000000 : ℝ), (5817283597517/12500000000000 : ℝ), (1740061328431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275235321/10000000000 : ℝ)|^5011 ≤ (44761424566601/100000000000000 : ℝ)^3987
        have hw : |(5275235321/10000000000 : ℝ)|=(5275235321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272059159/500000000 : ℝ)|^5011 ≤ (5817283597517/12500000000000 : ℝ)^3987
        have hw : |(272059159/500000000 : ℝ)|=(272059159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-716491647/5000000000 : ℝ)|^5011 ≤ (1740061328431/20000000000000 : ℝ)^3987
        have hw : |(-716491647/5000000000 : ℝ)|=(716491647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1673_s2_7 (p : ℝ) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520413207/1250000000 : ℝ)*x 0 + (902820617/2000000000 : ℝ)*x 1 + (9581061/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520413207/1250000000 : ℝ)^5011 ≤ (16621371064029/50000000000000 : ℝ)^3987 := by
    have hnat : (520413207 : ℕ)^5011*50000000000000^3987 ≤ 16621371064029^3987*1250000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520413207 1250000000 16621371064029 50000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902820617/2000000000 : ℝ)^5011 ≤ (7360095194779/20000000000000 : ℝ)^3987 := by
    have hnat : (902820617 : ℕ)^5011*20000000000000^3987 ≤ 7360095194779^3987*2000000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902820617 2000000000 7360095194779 20000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9581061/25000000 : ℝ)^5011 ≤ (29956781884061/100000000000000 : ℝ)^3987 := by
    have hnat : (9581061 : ℕ)^5011*100000000000000^3987 ≤ 29956781884061^3987*25000000^5011 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9581061 25000000 29956781884061 100000000000000 5011 3987 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5011/1024 : ℝ)) 5011 3987 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520413207/1250000000 : ℝ), (902820617/2000000000 : ℝ), (9581061/25000000 : ℝ)] ![(16621371064029/50000000000000 : ℝ), (7360095194779/20000000000000 : ℝ), (29956781884061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520413207/1250000000 : ℝ)|^5011 ≤ (16621371064029/50000000000000 : ℝ)^3987
        have hw : |(520413207/1250000000 : ℝ)|=(520413207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902820617/2000000000 : ℝ)|^5011 ≤ (7360095194779/20000000000000 : ℝ)^3987
        have hw : |(902820617/2000000000 : ℝ)|=(902820617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9581061/25000000 : ℝ)|^5011 ≤ (29956781884061/100000000000000 : ℝ)^3987
        have hw : |(9581061/25000000 : ℝ)|=(9581061/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1673_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3409/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5023/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (671/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8137/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3409/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5023/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3409/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5023/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3409/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5023/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3409/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5023/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3409/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5023/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3409/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5023/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5023/50000 : ℝ) ^ (5007/1024 : ℝ) ≤ (26371053355469/2000000000000000000 : ℝ) := by
    have hpowers : (5023/50000 : ℝ)^5007 ≤ (26371053355469/2000000000000000000 : ℝ)^1024 := by
      have hnat : (5023 : ℕ)^5007*2000000000000000000^1024 ≤ 26371053355469^1024*50000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5023 50000 26371053355469 2000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5023/50000 : ℝ)) (X := (26371053355469/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3409/20000 : ℝ) ^ (5007/1024 : ℝ) ≤ (8744792387354219/50000000000000000000 : ℝ) := by
    have hpowers : (3409/20000 : ℝ)^5007 ≤ (8744792387354219/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3409 : ℕ)^5007*50000000000000000000^1024 ≤ 8744792387354219^1024*20000^5007 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3409 20000 8744792387354219 50000000000000000000 5007 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3409/20000 : ℝ)) (X := (8744792387354219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000026371053355469/1000000000000000000 : ℝ) ≤ (10000053931846213/10000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (1000026371053355469/1000000000000000000 : ℝ)^1024 ≤ (10000053931846213/10000000000000000 : ℝ)^5007 := by
      have hnat : (1000026371053355469 : ℕ)^1024*10000000000000000^5007 ≤ 10000053931846213^5007*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000026371053355469 1000000000000000000 10000053931846213 10000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000053931846213/10000000000000000 : ℝ)) (X := (1000026371053355469/1000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125587754295077559/3125000000000000000 : ℝ) ≤ (5000192311684987/5000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (3125587754295077559/3125000000000000000 : ℝ)^1024 ≤ (5000192311684987/5000000000000000 : ℝ)^5007 := by
      have hnat : (3125587754295077559 : ℕ)^1024*5000000000000000^5007 ≤ 5000192311684987^5007*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125587754295077559 3125000000000000000 5000192311684987 5000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000192311684987/5000000000000000 : ℝ)) (X := (3125587754295077559/3125000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008744792387354219/25000000000000000000 : ℝ) ≤ (2000143062978747/2000000000000000 : ℝ) ^ (5007/1024 : ℝ) := by
    have hpowers : (25008744792387354219/25000000000000000000 : ℝ)^1024 ≤ (2000143062978747/2000000000000000 : ℝ)^5007 := by
      have hnat : (25008744792387354219 : ℕ)^1024*2000000000000000^5007 ≤ 2000143062978747^5007*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008744792387354219 25000000000000000000 2000143062978747 2000000000000000 1024 5007 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000143062978747/2000000000000000 : ℝ)) (X := (25008744792387354219/25000000000000000000 : ℝ)) (by norm_num) 5007 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26371053355469/2000000000000000000 : ℝ) ≤ ((2799349328595849551/2799600000000000000 : ℝ)+2*(330691523761/699900000000000 : ℝ)*(5023/50000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (2799349328595849551/2799600000000000000 : ℝ)+2*(330691523761/699900000000000 : ℝ)*(5023/50000 : ℝ)=(10000053931846213/10000000000000000 : ℝ) by norm_num, show 1+2*(26371053355469/2000000000000000000 : ℝ)=(1000026371053355469/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8744792387354219/50000000000000000000 : ℝ)+(26371053355469/2000000000000000000 : ℝ) ≤ ((2799349328595849551/2799600000000000000 : ℝ)+(330691523761/699900000000000 : ℝ)*((3409/20000 : ℝ)+(5023/50000 : ℝ)))^(5007/1024 : ℝ) := by
    rw [show (2799349328595849551/2799600000000000000 : ℝ)+(330691523761/699900000000000 : ℝ)*((3409/20000 : ℝ)+(5023/50000 : ℝ))=(5000192311684987/5000000000000000 : ℝ) by norm_num, show 1+(8744792387354219/50000000000000000000 : ℝ)+(26371053355469/2000000000000000000 : ℝ)=(3125587754295077559/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8744792387354219/50000000000000000000 : ℝ) ≤ ((2799349328595849551/2799600000000000000 : ℝ)+2*(330691523761/699900000000000 : ℝ)*(3409/20000 : ℝ))^(5007/1024 : ℝ) := by
    rw [show (2799349328595849551/2799600000000000000 : ℝ)+2*(330691523761/699900000000000 : ℝ)*(3409/20000 : ℝ)=(2000143062978747/2000000000000000 : ℝ) by norm_num, show 1+2*(8744792387354219/50000000000000000000 : ℝ)=(25008744792387354219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2799349328595849551/2799600000000000000 : ℝ)*(X 1 0+X 2 0)+(330691523761/699900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (5023/50000 : ℝ)) (hi := (3409/20000 : ℝ)) (c := (2799349328595849551/2799600000000000000 : ℝ)) (alpha := (330691523761/699900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2799349328595849551/2799600000000000000 : ℝ)*(X 0 1+X 2 1)+(330691523761/699900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (5023/50000 : ℝ)) (hi := (3409/20000 : ℝ)) (c := (2799349328595849551/2799600000000000000 : ℝ)) (alpha := (330691523761/699900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2799349328595849551/2799600000000000000 : ℝ)*(X 0 2+X 1 2)+(330691523761/699900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5007/1024 : ℝ)) (lo := (5023/50000 : ℝ)) (hi := (3409/20000 : ℝ)) (c := (2799349328595849551/2799600000000000000 : ℝ)) (alpha := (330691523761/699900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-778599969/5000000000 : ℝ)*X 0 0+(2721613419/5000000000 : ℝ)*X 0 1+(5183117389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344892669/10000000000 : ℝ)*X 1 0+(-845524263/5000000000 : ℝ)*X 1 1+(323944837/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534489251/1000000000 : ℝ)*X 2 0+(1036623489/2000000000 : ℝ)*X 2 1+(-169104867/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((520391757/1250000000 : ℝ)*X 0 0+(1913491059/5000000000 : ℝ)*X 0 1+(2259743789/5000000000 : ℝ)*X 0 2+(520391757/1250000000 : ℝ)*X 1 0+(1913491059/5000000000 : ℝ)*X 1 1+(2259743789/5000000000 : ℝ)*X 1 2+(520391757/1250000000 : ℝ)*X 2 0+(1913491059/5000000000 : ℝ)*X 2 1+(2259743789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1557265203/10000000000 : ℝ)*X 0 0+(162035603/312500000 : ℝ)*X 0 1+(1360295669/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275236453/10000000000 : ℝ)*X 1 0+(-358245709/2500000000 : ℝ)*X 1 1+(2720591191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275235321/10000000000 : ℝ)*X 2 0+(272059159/500000000 : ℝ)*X 2 1+(-716491647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((520413207/1250000000 : ℝ)*X 0 0+(902820617/2000000000 : ℝ)*X 0 1+(9581061/25000000 : ℝ)*X 0 2+(520413207/1250000000 : ℝ)*X 1 0+(902820617/2000000000 : ℝ)*X 1 1+(9581061/25000000 : ℝ)*X 1 2+(520413207/1250000000 : ℝ)*X 2 0+(902820617/2000000000 : ℝ)*X 2 1+(9581061/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1673_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12529249395784510227043/2333000000000000000000000000 : ℝ) := by norm_num
    linear_combination (843764459/100000000000000 : ℝ)*(base19) + (691267413/100000000000000 : ℝ)*(base23) + (2037961/10000000000000 : ℝ)*(lower2) + (24727783/12500000000000 : ℝ)*(upper3) + (962007/2500000000000 : ℝ)*(upper5) + (13221488265739/500000000000 : ℝ)*(major0) + (13221488265739/500000000000 : ℝ)*(major1) + (13221488265739/500000000000 : ℝ)*(major2) + (1922273772937097/50000000000000 : ℝ)*(sp0) + (1922277415191893/50000000000000 : ℝ)*(sp1) + (3844554982880831/100000000000000 : ℝ)*(sp2) + (722017547937677/50000000000000 : ℝ)*(sp3) + (162565481/2000000000000 : ℝ)*(sp4) + (2178628571/50000000000000 : ℝ)*(sp7) + (288807890626499/20000000000000 : ℝ)*(f.failure) + (961138918537061/25000000000000 : ℝ)*(f.sum) + (24144007516993/3499500000000000000000000000 : ℝ)*base66 + (3026856175930663/466600000000000000000000000000 : ℝ)*base67 + (514381069028263/466600000000000000000000000000 : ℝ)*base69 + (665548207162937/466600000000000000000000000000 : ℝ)*base72 + (7044115468283/3499500000000000000000000000 : ℝ)*base73 + (1577521506515337/466600000000000000000000000000 : ℝ)*base76 + (1393739111435463/466600000000000000000000000000 : ℝ)*base77 + (354925040841137/466600000000000000000000000000 : ℝ)*base80 + (16254048073099/3499500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (21588603/2000000000000000000000 : ℝ)*base90 + (21588603/2000000000000000000000 : ℝ)*base92 + (21588603/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (235468877224278275627041067/23330000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (322389761/12500000000000 : ℝ)*(base19) + (1084627501/50000000000000 : ℝ)*(base23) + (271972243/100000000000000 : ℝ)*(upper2) + (13381873/5000000000000 : ℝ)*(upper3) + (121834033/25000000000000 : ℝ)*(upper5) + (1343137039512761/50000000000000 : ℝ)*(major0) + (1343137039512761/50000000000000 : ℝ)*(major1) + (1343137039512761/50000000000000 : ℝ)*(major2) + (15370376883/50000000000000 : ℝ)*(sp1) + (24126116957/100000000000000 : ℝ)*(sp2) + (3905585224793839/100000000000000 : ℝ)*(sp4) + (30512124257203/781250000000 : ℝ)*(sp5) + (3905558929421879/100000000000000 : ℝ)*(sp6) + (22921290575391/1562500000000 : ℝ)*(sp7) + (22921290575391/1562500000000 : ℝ)*(f.failure) + (3905585224793839/100000000000000 : ℝ)*(f.sum) + (123422921259623/34995000000000000000000000000 : ℝ)*base66 + (135550064308261437/46660000000000000000000000000000 : ℝ)*base67 + (668648852057461437/46660000000000000000000000000000 : ℝ)*base69 + (498132626318701437/46660000000000000000000000000000 : ℝ)*base71 + (47560043827129/17497500000000000000000000000 : ℝ)*base74 + (494558012584101437/46660000000000000000000000000000 : ℝ)*base75 + (147302804285521437/46660000000000000000000000000000 : ℝ)*base77 + (743146657813201437/46660000000000000000000000000000 : ℝ)*base79 + (66269671491581/17497500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (278273/156250000000000000000 : ℝ)*base89 + (278273/156250000000000000000 : ℝ)*base91 + (278273/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1673_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3409/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5023/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1673_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1673_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1673_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1673_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1673_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5007/1024 : ℝ) ≤ p) (hpb : p ≤ (5011/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183118103/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8137/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1673_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
