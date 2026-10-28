-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:45:15.045266+00:00
-- url     : https://prove2.me/submissions/4db9b1e7-be58-4a39-9b1f-9499b6fa2e91

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
theorem support_rectangle_w1171_s3_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074798997/5000000000 : ℝ)*x 0 + (5426263657/10000000000 : ℝ)*x 1 + (2617364977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074798997/5000000000 : ℝ)^2091 ≤ (13057804878877/100000000000000 : ℝ)^1579 := by
    have hnat : (1074798997 : ℕ)^2091*100000000000000^1579 ≤ 13057804878877^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074798997 5000000000 13057804878877 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426263657/10000000000 : ℝ)^2091 ≤ (22252625297857/50000000000000 : ℝ)^1579 := by
    have hnat : (5426263657 : ℕ)^2091*50000000000000^1579 ≤ 22252625297857^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426263657 10000000000 22252625297857 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617364977/5000000000 : ℝ)^2091 ≤ (42436944507147/100000000000000 : ℝ)^1579 := by
    have hnat : (2617364977 : ℕ)^2091*100000000000000^1579 ≤ 42436944507147^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617364977 5000000000 42436944507147 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074798997/5000000000 : ℝ), (5426263657/10000000000 : ℝ), (2617364977/5000000000 : ℝ)] ![(13057804878877/100000000000000 : ℝ), (22252625297857/50000000000000 : ℝ), (42436944507147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074798997/5000000000 : ℝ)|^2091 ≤ (13057804878877/100000000000000 : ℝ)^1579
        have hw : |(-1074798997/5000000000 : ℝ)|=(1074798997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426263657/10000000000 : ℝ)|^2091 ≤ (22252625297857/50000000000000 : ℝ)^1579
        have hw : |(5426263657/10000000000 : ℝ)|=(5426263657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617364977/5000000000 : ℝ)|^2091 ≤ (42436944507147/100000000000000 : ℝ)^1579
        have hw : |(2617364977/5000000000 : ℝ)|=(2617364977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353106933/10000000000 : ℝ)*x 0 + (-561860737/2500000000 : ℝ)*x 1 + (5234729757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353106933/10000000000 : ℝ)^2091 ≤ (43712414737907/100000000000000 : ℝ)^1579 := by
    have hnat : (5353106933 : ℕ)^2091*100000000000000^1579 ≤ 43712414737907^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353106933 10000000000 43712414737907 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561860737/2500000000 : ℝ)^2091 ≤ (13850642860151/100000000000000 : ℝ)^1579 := by
    have hnat : (561860737 : ℕ)^2091*100000000000000^1579 ≤ 13850642860151^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561860737 2500000000 13850642860151 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234729757/10000000000 : ℝ)^2091 ≤ (663077224879/1562500000000 : ℝ)^1579 := by
    have hnat : (5234729757 : ℕ)^2091*1562500000000^1579 ≤ 663077224879^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234729757 10000000000 663077224879 1562500000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353106933/10000000000 : ℝ), (-561860737/2500000000 : ℝ), (5234729757/10000000000 : ℝ)] ![(43712414737907/100000000000000 : ℝ), (13850642860151/100000000000000 : ℝ), (663077224879/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353106933/10000000000 : ℝ)|^2091 ≤ (43712414737907/100000000000000 : ℝ)^1579
        have hw : |(5353106933/10000000000 : ℝ)|=(5353106933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561860737/2500000000 : ℝ)|^2091 ≤ (13850642860151/100000000000000 : ℝ)^1579
        have hw : |(-561860737/2500000000 : ℝ)|=(561860737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234729757/10000000000 : ℝ)|^2091 ≤ (663077224879/1562500000000 : ℝ)^1579
        have hw : |(5234729757/10000000000 : ℝ)|=(5234729757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353107017/10000000000 : ℝ)*x 0 + (2617364877/5000000000 : ℝ)*x 1 + (-56186071/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353107017/10000000000 : ℝ)^2091 ≤ (34969932517/80000000000 : ℝ)^1579 := by
    have hnat : (5353107017 : ℕ)^2091*80000000000^1579 ≤ 34969932517^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353107017 10000000000 34969932517 80000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617364877/5000000000 : ℝ)^2091 ≤ (848738847201/2000000000000 : ℝ)^1579 := by
    have hnat : (2617364877 : ℕ)^2091*2000000000000^1579 ≤ 848738847201^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617364877 5000000000 848738847201 2000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56186071/250000000 : ℝ)^2091 ≤ (1731330247343/12500000000000 : ℝ)^1579 := by
    have hnat : (56186071 : ℕ)^2091*12500000000000^1579 ≤ 1731330247343^1579*250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56186071 250000000 1731330247343 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353107017/10000000000 : ℝ), (2617364877/5000000000 : ℝ), (-56186071/250000000 : ℝ)] ![(34969932517/80000000000 : ℝ), (848738847201/2000000000000 : ℝ), (1731330247343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353107017/10000000000 : ℝ)|^2091 ≤ (34969932517/80000000000 : ℝ)^1579
        have hw : |(5353107017/10000000000 : ℝ)|=(5353107017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617364877/5000000000 : ℝ)|^2091 ≤ (848738847201/2000000000000 : ℝ)^1579
        have hw : |(2617364877/5000000000 : ℝ)|=(2617364877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56186071/250000000 : ℝ)|^2091 ≤ (1731330247343/12500000000000 : ℝ)^1579
        have hw : |(-56186071/250000000 : ℝ)|=(56186071/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (544815511/1250000000 : ℝ)*x 0 + (521383937/1250000000 : ℝ)*x 1 + (227714579/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544815511/1250000000 : ℝ)^2091 ≤ (4162010461993/12500000000000 : ℝ)^1579 := by
    have hnat : (544815511 : ℕ)^2091*12500000000000^1579 ≤ 4162010461993^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544815511 1250000000 4162010461993 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521383937/1250000000 : ℝ)^2091 ≤ (1963318334081/6250000000000 : ℝ)^1579 := by
    have hnat : (521383937 : ℕ)^2091*6250000000000^1579 ≤ 1963318334081^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521383937 1250000000 1963318334081 6250000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227714579/500000000 : ℝ)^2091 ≤ (17645411475299/50000000000000 : ℝ)^1579 := by
    have hnat : (227714579 : ℕ)^2091*50000000000000^1579 ≤ 17645411475299^1579*500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227714579 500000000 17645411475299 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544815511/1250000000 : ℝ), (521383937/1250000000 : ℝ), (227714579/500000000 : ℝ)] ![(4162010461993/12500000000000 : ℝ), (1963318334081/6250000000000 : ℝ), (17645411475299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544815511/1250000000 : ℝ)|^2091 ≤ (4162010461993/12500000000000 : ℝ)^1579
        have hw : |(544815511/1250000000 : ℝ)|=(544815511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521383937/1250000000 : ℝ)|^2091 ≤ (1963318334081/6250000000000 : ℝ)^1579
        have hw : |(521383937/1250000000 : ℝ)|=(521383937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227714579/500000000 : ℝ)|^2091 ≤ (17645411475299/50000000000000 : ℝ)^1579
        have hw : |(227714579/500000000 : ℝ)|=(227714579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074807329/5000000000 : ℝ)*x 0 + (130886459/250000000 : ℝ)*x 1 + (1356382829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074807329/5000000000 : ℝ)^2091 ≤ (6528969464101/50000000000000 : ℝ)^1579 := by
    have hnat : (1074807329 : ℕ)^2091*50000000000000^1579 ≤ 6528969464101^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074807329 5000000000 6528969464101 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130886459/250000000 : ℝ)^2091 ≤ (42444764476281/100000000000000 : ℝ)^1579 := by
    have hnat : (130886459 : ℕ)^2091*100000000000000^1579 ≤ 42444764476281^1579*250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130886459 250000000 42444764476281 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356382829/2500000000 : ℝ)^2091 ≤ (44497296586181/100000000000000 : ℝ)^1579 := by
    have hnat : (1356382829 : ℕ)^2091*100000000000000^1579 ≤ 44497296586181^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356382829 2500000000 44497296586181 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074807329/5000000000 : ℝ), (130886459/250000000 : ℝ), (1356382829/2500000000 : ℝ)] ![(6528969464101/50000000000000 : ℝ), (42444764476281/100000000000000 : ℝ), (44497296586181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074807329/5000000000 : ℝ)|^2091 ≤ (6528969464101/50000000000000 : ℝ)^1579
        have hw : |(-1074807329/5000000000 : ℝ)|=(1074807329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130886459/250000000 : ℝ)|^2091 ≤ (42444764476281/100000000000000 : ℝ)^1579
        have hw : |(130886459/250000000 : ℝ)|=(130886459/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356382829/2500000000 : ℝ)|^2091 ≤ (44497296586181/100000000000000 : ℝ)^1579
        have hw : |(1356382829/2500000000 : ℝ)|=(1356382829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326120173/2500000000 : ℝ)*x 0 + (-257080259/1250000000 : ℝ)*x 1 + (5425531131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326120173/2500000000 : ℝ)^2091 ≤ (8637473084749/20000000000000 : ℝ)^1579 := by
    have hnat : (1326120173 : ℕ)^2091*20000000000000^1579 ≤ 8637473084749^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326120173 2500000000 8637473084749 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257080259/1250000000 : ℝ)^2091 ≤ (6157669992477/50000000000000 : ℝ)^1579 := by
    have hnat : (257080259 : ℕ)^2091*50000000000000^1579 ≤ 6157669992477^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257080259 1250000000 6157669992477 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425531131/10000000000 : ℝ)^2091 ≤ (44497294576927/100000000000000 : ℝ)^1579 := by
    have hnat : (5425531131 : ℕ)^2091*100000000000000^1579 ≤ 44497294576927^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425531131 10000000000 44497294576927 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326120173/2500000000 : ℝ), (-257080259/1250000000 : ℝ), (5425531131/10000000000 : ℝ)] ![(8637473084749/20000000000000 : ℝ), (6157669992477/50000000000000 : ℝ), (44497294576927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326120173/2500000000 : ℝ)|^2091 ≤ (8637473084749/20000000000000 : ℝ)^1579
        have hw : |(1326120173/2500000000 : ℝ)|=(1326120173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257080259/1250000000 : ℝ)|^2091 ≤ (6157669992477/50000000000000 : ℝ)^1579
        have hw : |(-257080259/1250000000 : ℝ)|=(257080259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425531131/10000000000 : ℝ)|^2091 ≤ (44497294576927/100000000000000 : ℝ)^1579
        have hw : |(5425531131/10000000000 : ℝ)|=(5425531131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326120483/2500000000 : ℝ)*x 0 + (5425530021/10000000000 : ℝ)*x 1 + (-1028320953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326120483/2500000000 : ℝ)^2091 ≤ (43187378793007/100000000000000 : ℝ)^1579 := by
    have hnat : (1326120483 : ℕ)^2091*100000000000000^1579 ≤ 43187378793007^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326120483 2500000000 43187378793007 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425530021/10000000000 : ℝ)^2091 ≤ (44497282521399/100000000000000 : ℝ)^1579 := by
    have hnat : (5425530021 : ℕ)^2091*100000000000000^1579 ≤ 44497282521399^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425530021 10000000000 44497282521399 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028320953/5000000000 : ℝ)^2091 ≤ (2463067733723/20000000000000 : ℝ)^1579 := by
    have hnat : (1028320953 : ℕ)^2091*20000000000000^1579 ≤ 2463067733723^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028320953 5000000000 2463067733723 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326120483/2500000000 : ℝ), (5425530021/10000000000 : ℝ), (-1028320953/5000000000 : ℝ)] ![(43187378793007/100000000000000 : ℝ), (44497282521399/100000000000000 : ℝ), (2463067733723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326120483/2500000000 : ℝ)|^2091 ≤ (43187378793007/100000000000000 : ℝ)^1579
        have hw : |(1326120483/2500000000 : ℝ)|=(1326120483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425530021/10000000000 : ℝ)|^2091 ≤ (44497282521399/100000000000000 : ℝ)^1579
        have hw : |(5425530021/10000000000 : ℝ)|=(5425530021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028320953/5000000000 : ℝ)|^2091 ≤ (2463067733723/20000000000000 : ℝ)^1579
        have hw : |(-1028320953/5000000000 : ℝ)|=(1028320953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s3_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2179278569/5000000000 : ℝ)*x 0 + (2276417239/5000000000 : ℝ)*x 1 + (2086268519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179278569/5000000000 : ℝ)^2091 ≤ (33296418043077/100000000000000 : ℝ)^1579 := by
    have hnat : (2179278569 : ℕ)^2091*100000000000000^1579 ≤ 33296418043077^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179278569 5000000000 33296418043077 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276417239/5000000000 : ℝ)^2091 ≤ (7055174320993/20000000000000 : ℝ)^1579 := by
    have hnat : (2276417239 : ℕ)^2091*20000000000000^1579 ≤ 7055174320993^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276417239 5000000000 7055174320993 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086268519/5000000000 : ℝ)^2091 ≤ (31427710336297/100000000000000 : ℝ)^1579 := by
    have hnat : (2086268519 : ℕ)^2091*100000000000000^1579 ≤ 31427710336297^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086268519 5000000000 31427710336297 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179278569/5000000000 : ℝ), (2276417239/5000000000 : ℝ), (2086268519/5000000000 : ℝ)] ![(33296418043077/100000000000000 : ℝ), (7055174320993/20000000000000 : ℝ), (31427710336297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179278569/5000000000 : ℝ)|^2091 ≤ (33296418043077/100000000000000 : ℝ)^1579
        have hw : |(2179278569/5000000000 : ℝ)|=(2179278569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2276417239/5000000000 : ℝ)|^2091 ≤ (7055174320993/20000000000000 : ℝ)^1579
        have hw : |(2276417239/5000000000 : ℝ)|=(2276417239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086268519/5000000000 : ℝ)|^2091 ≤ (31427710336297/100000000000000 : ℝ)^1579
        have hw : |(2086268519/5000000000 : ℝ)|=(2086268519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8209/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10719/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3693/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8209/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8209/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9199/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8209/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8209/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9199/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8209/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8209/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9199/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9199/100000 : ℝ) ^ (8363/2048 : ℝ) ≤ (1466826926409731/25000000000000000000 : ℝ) := by
    have hpowers : (9199/100000 : ℝ)^8363 ≤ (1466826926409731/25000000000000000000 : ℝ)^2048 := by
      have hnat : (9199 : ℕ)^8363*25000000000000000000^2048 ≤ 1466826926409731^2048*100000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9199 100000 1466826926409731 25000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9199/100000 : ℝ)) (X := (1466826926409731/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8209/50000 : ℝ) ^ (8363/2048 : ℝ) ≤ (7810400866225347/12500000000000000000 : ℝ) := by
    have hpowers : (8209/50000 : ℝ)^8363 ≤ (7810400866225347/12500000000000000000 : ℝ)^2048 := by
      have hnat : (8209 : ℕ)^8363*12500000000000000000^2048 ≤ 7810400866225347^2048*50000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8209 50000 7810400866225347 12500000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8209/50000 : ℝ)) (X := (7810400866225347/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501466826926409731/12500000000000000000 : ℝ) ≤ (625017959634463/625000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (12501466826926409731/12500000000000000000 : ℝ)^2048 ≤ (625017959634463/625000000000000 : ℝ)^8363 := by
      have hnat : (12501466826926409731 : ℕ)^2048*625000000000000^8363 ≤ 625017959634463^8363*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501466826926409731 12500000000000000000 625017959634463 625000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017959634463/625000000000000 : ℝ)) (X := (12501466826926409731/12500000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000683505146354417/1000000000000000000 : ℝ) ≤ (10001673391659671/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (1000683505146354417/1000000000000000000 : ℝ)^2048 ≤ (10001673391659671/10000000000000000 : ℝ)^8363 := by
      have hnat : (1000683505146354417 : ℕ)^2048*10000000000000000^8363 ≤ 10001673391659671^8363*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000683505146354417 1000000000000000000 10001673391659671 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001673391659671/10000000000000000 : ℝ)) (X := (1000683505146354417/1000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6257810400866225347/6250000000000000000 : ℝ) ≤ (5001529714583967/5000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (6257810400866225347/6250000000000000000 : ℝ)^2048 ≤ (5001529714583967/5000000000000000 : ℝ)^8363 := by
      have hnat : (6257810400866225347 : ℕ)^2048*5000000000000000^8363 ≤ 5001529714583967^8363*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6257810400866225347 6250000000000000000 5001529714583967 5000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001529714583967/5000000000000000 : ℝ)) (X := (6257810400866225347/6250000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1466826926409731/25000000000000000000 : ℝ) ≤ ((36083287045770995839/36095000000000000000 : ℝ)+2*(1386037508263/721900000000000 : ℝ)*(9199/100000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (36083287045770995839/36095000000000000000 : ℝ)+2*(1386037508263/721900000000000 : ℝ)*(9199/100000 : ℝ)=(625017959634463/625000000000000 : ℝ) by norm_num, show 1+2*(1466826926409731/25000000000000000000 : ℝ)=(12501466826926409731/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7810400866225347/12500000000000000000 : ℝ)+(1466826926409731/25000000000000000000 : ℝ) ≤ ((36083287045770995839/36095000000000000000 : ℝ)+(1386037508263/721900000000000 : ℝ)*((8209/50000 : ℝ)+(9199/100000 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (36083287045770995839/36095000000000000000 : ℝ)+(1386037508263/721900000000000 : ℝ)*((8209/50000 : ℝ)+(9199/100000 : ℝ))=(10001673391659671/10000000000000000 : ℝ) by norm_num, show 1+(7810400866225347/12500000000000000000 : ℝ)+(1466826926409731/25000000000000000000 : ℝ)=(1000683505146354417/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7810400866225347/12500000000000000000 : ℝ) ≤ ((36083287045770995839/36095000000000000000 : ℝ)+2*(1386037508263/721900000000000 : ℝ)*(8209/50000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (36083287045770995839/36095000000000000000 : ℝ)+2*(1386037508263/721900000000000 : ℝ)*(8209/50000 : ℝ)=(5001529714583967/5000000000000000 : ℝ) by norm_num, show 1+2*(7810400866225347/12500000000000000000 : ℝ)=(6257810400866225347/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36083287045770995839/36095000000000000000 : ℝ)*(X 1 0+X 2 0)+(1386037508263/721900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (9199/100000 : ℝ)) (hi := (8209/50000 : ℝ)) (c := (36083287045770995839/36095000000000000000 : ℝ)) (alpha := (1386037508263/721900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36083287045770995839/36095000000000000000 : ℝ)*(X 0 1+X 2 1)+(1386037508263/721900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (9199/100000 : ℝ)) (hi := (8209/50000 : ℝ)) (c := (36083287045770995839/36095000000000000000 : ℝ)) (alpha := (1386037508263/721900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36083287045770995839/36095000000000000000 : ℝ)*(X 0 2+X 1 2)+(1386037508263/721900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (9199/100000 : ℝ)) (hi := (8209/50000 : ℝ)) (c := (36083287045770995839/36095000000000000000 : ℝ)) (alpha := (1386037508263/721900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1074798997/5000000000 : ℝ)*X 0 0+(5426263657/10000000000 : ℝ)*X 0 1+(2617364977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353106933/10000000000 : ℝ)*X 1 0+(-561860737/2500000000 : ℝ)*X 1 1+(5234729757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353107017/10000000000 : ℝ)*X 2 0+(2617364877/5000000000 : ℝ)*X 2 1+(-56186071/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544815511/1250000000 : ℝ)*X 0 0+(521383937/1250000000 : ℝ)*X 0 1+(227714579/500000000 : ℝ)*X 0 2+(544815511/1250000000 : ℝ)*X 1 0+(521383937/1250000000 : ℝ)*X 1 1+(227714579/500000000 : ℝ)*X 1 2+(544815511/1250000000 : ℝ)*X 2 0+(521383937/1250000000 : ℝ)*X 2 1+(227714579/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074807329/5000000000 : ℝ)*X 0 0+(130886459/250000000 : ℝ)*X 0 1+(1356382829/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326120173/2500000000 : ℝ)*X 1 0+(-257080259/1250000000 : ℝ)*X 1 1+(5425531131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326120483/2500000000 : ℝ)*X 2 0+(5425530021/10000000000 : ℝ)*X 2 1+(-1028320953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179278569/5000000000 : ℝ)*X 0 0+(2276417239/5000000000 : ℝ)*X 0 1+(2086268519/5000000000 : ℝ)*X 0 2+(2179278569/5000000000 : ℝ)*X 1 0+(2276417239/5000000000 : ℝ)*X 1 1+(2086268519/5000000000 : ℝ)*X 1 2+(2179278569/5000000000 : ℝ)*X 2 0+(2276417239/5000000000 : ℝ)*X 2 1+(2086268519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1540647395179654494583067247/225593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1646817897/100000000000000 : ℝ)*(base19) + (1593038753/100000000000000 : ℝ)*(base23) + (145291/200000000000 : ℝ)*(lower2) + (70543349/50000000000000 : ℝ)*(upper3) + (42387463/25000000000000 : ℝ)*(upper5) + (489410045360941/12500000000000 : ℝ)*(major0) + (489410045360941/12500000000000 : ℝ)*(major1) + (3915280362887529/100000000000000 : ℝ)*(major2) + (5221038466019721/100000000000000 : ℝ)*(sp0) + (1044213032683727/20000000000000 : ℝ)*(sp1) + (2610532608598889/50000000000000 : ℝ)*(sp2) + (521895974407197/20000000000000 : ℝ)*(sp3) + (28344216811/100000000000000 : ℝ)*(sp4) + (13815859199/100000000000000 : ℝ)*(sp7) + (163093355493449/6250000000000 : ℝ)*(f.failure) + (1305266702559133/25000000000000 : ℝ)*(f.sum) + (208350988908291/72190000000000000000000000000 : ℝ)*base65 + (6989048076737644251/451187500000000000000000000000000 : ℝ)*base68 + (12973755130643191831/3609500000000000000000000000000000 : ℝ)*base69 + (4609259273206519251/451187500000000000000000000000000 : ℝ)*base72 + (326031743218611/72190000000000000000000000000 : ℝ)*base73 + (9532363808414308169/3609500000000000000000000000000000 : ℝ)*base76 + (3734139850188774499/451187500000000000000000000000000 : ℝ)*base77 + (1894426886048350501/451187500000000000000000000000000 : ℝ)*base80 + (37574933722187/18047500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (369469/78125000000000000000 : ℝ)*base89 + (369469/78125000000000000000 : ℝ)*base91 + (411781/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12857557250972177188137771/5639843750000000000000000000000 : ℝ) := by norm_num
    linear_combination (142446541/12500000000000 : ℝ)*(base23) + (20643359/100000000000000 : ℝ)*(lower2) + (5062047/12500000000000 : ℝ)*(lower3) + (57008993/100000000000000 : ℝ)*(upper4) + (1972671304851081/50000000000000 : ℝ)*(major0) + (1972671304851081/50000000000000 : ℝ)*(major1) + (986335652425541/25000000000000 : ℝ)*(major2) + (23271501/781250000000 : ℝ)*(sp0) + (1223778679/20000000000000 : ℝ)*(sp2) + (479556481/20000000000000 : ℝ)*(sp3) + (5261152301564903/100000000000000 : ℝ)*(sp4) + (5261155280317031/100000000000000 : ℝ)*(sp5) + (5261148021851309/100000000000000 : ℝ)*(sp6) + (2629527465312473/100000000000000 : ℝ)*(sp7) + (1314764931547439/50000000000000 : ℝ)*(f.failure) + (5261155280317031/100000000000000 : ℝ)*(f.sum) + (911152195893391/36095000000000000000000000000 : ℝ)*base66 + (18806462301468548041/1804750000000000000000000000000000 : ℝ)*base68 + (4465428009157648899/902375000000000000000000000000000 : ℝ)*base69 + (155653428972294548041/1804750000000000000000000000000000 : ℝ)*base72 + (27300867105379/36095000000000000000000000000 : ℝ)*base73 + (7872662817705273899/902375000000000000000000000000000 : ℝ)*base75 + (11797954221699948041/1804750000000000000000000000000000 : ℝ)*base78 + (35960377972210948041/1804750000000000000000000000000000 : ℝ)*base80 + (72113792236603/18047500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6543659/625000000000000000000 : ℝ)*base89 + (6543659/625000000000000000000 : ℝ)*base91 + (5956341/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1171_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8209/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1171_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1171_s4_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-430475379/2000000000 : ℝ)*x 0 + (337533473/625000000 : ℝ)*x 1 + (5258639169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430475379/2000000000 : ℝ)^2091 ≤ (2616032739911/20000000000000 : ℝ)^1579 := by
    have hnat : (430475379 : ℕ)^2091*20000000000000^1579 ≤ 2616032739911^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430475379 2000000000 2616032739911 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337533473/625000000 : ℝ)^2091 ≤ (44226024851477/100000000000000 : ℝ)^1579 := by
    have hnat : (337533473 : ℕ)^2091*100000000000000^1579 ≤ 44226024851477^1579*625000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337533473 625000000 44226024851477 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258639169/10000000000 : ℝ)^2091 ≤ (5336726429511/12500000000000 : ℝ)^1579 := by
    have hnat : (5258639169 : ℕ)^2091*12500000000000^1579 ≤ 5336726429511^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258639169 10000000000 5336726429511 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430475379/2000000000 : ℝ), (337533473/625000000 : ℝ), (5258639169/10000000000 : ℝ)] ![(2616032739911/20000000000000 : ℝ), (44226024851477/100000000000000 : ℝ), (5336726429511/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430475379/2000000000 : ℝ)|^2091 ≤ (2616032739911/20000000000000 : ℝ)^1579
        have hw : |(-430475379/2000000000 : ℝ)|=(430475379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337533473/625000000 : ℝ)|^2091 ≤ (44226024851477/100000000000000 : ℝ)^1579
        have hw : |(337533473/625000000 : ℝ)|=(337533473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258639169/10000000000 : ℝ)|^2091 ≤ (5336726429511/12500000000000 : ℝ)^1579
        have hw : |(5258639169/10000000000 : ℝ)|=(5258639169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346663577/10000000000 : ℝ)*x 0 + (-278058379/1250000000 : ℝ)*x 1 + (5258638469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346663577/10000000000 : ℝ)^2091 ≤ (5455344048381/12500000000000 : ℝ)^1579 := by
    have hnat : (5346663577 : ℕ)^2091*12500000000000^1579 ≤ 5455344048381^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346663577 10000000000 5455344048381 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278058379/1250000000 : ℝ)^2091 ≤ (13663443696463/100000000000000 : ℝ)^1579 := by
    have hnat : (278058379 : ℕ)^2091*100000000000000^1579 ≤ 13663443696463^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278058379 1250000000 13663443696463 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5258638469/10000000000 : ℝ)^2091 ≤ (8538760782027/20000000000000 : ℝ)^1579 := by
    have hnat : (5258638469 : ℕ)^2091*20000000000000^1579 ≤ 8538760782027^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258638469 10000000000 8538760782027 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346663577/10000000000 : ℝ), (-278058379/1250000000 : ℝ), (5258638469/10000000000 : ℝ)] ![(5455344048381/12500000000000 : ℝ), (13663443696463/100000000000000 : ℝ), (8538760782027/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346663577/10000000000 : ℝ)|^2091 ≤ (5455344048381/12500000000000 : ℝ)^1579
        have hw : |(5346663577/10000000000 : ℝ)|=(5346663577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278058379/1250000000 : ℝ)|^2091 ≤ (13663443696463/100000000000000 : ℝ)^1579
        have hw : |(-278058379/1250000000 : ℝ)|=(278058379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5258638469/10000000000 : ℝ)|^2091 ≤ (8538760782027/20000000000000 : ℝ)^1579
        have hw : |(5258638469/10000000000 : ℝ)|=(5258638469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83541621/156250000 : ℝ)*x 0 + (1051727587/2000000000 : ℝ)*x 1 + (-444893503/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83541621/156250000 : ℝ)^2091 ≤ (5455344274027/12500000000000 : ℝ)^1579 := by
    have hnat : (83541621 : ℕ)^2091*12500000000000^1579 ≤ 5455344274027^1579*156250000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83541621 156250000 5455344274027 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051727587/2000000000 : ℝ)^2091 ≤ (42693798168909/100000000000000 : ℝ)^1579 := by
    have hnat : (1051727587 : ℕ)^2091*100000000000000^1579 ≤ 42693798168909^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051727587 2000000000 42693798168909 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444893503/2000000000 : ℝ)^2091 ≤ (13663447625203/100000000000000 : ℝ)^1579 := by
    have hnat : (444893503 : ℕ)^2091*100000000000000^1579 ≤ 13663447625203^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444893503 2000000000 13663447625203 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83541621/156250000 : ℝ), (1051727587/2000000000 : ℝ), (-444893503/2000000000 : ℝ)] ![(5455344274027/12500000000000 : ℝ), (42693798168909/100000000000000 : ℝ), (13663447625203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83541621/156250000 : ℝ)|^2091 ≤ (5455344274027/12500000000000 : ℝ)^1579
        have hw : |(83541621/156250000 : ℝ)|=(83541621/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051727587/2000000000 : ℝ)|^2091 ≤ (42693798168909/100000000000000 : ℝ)^1579
        have hw : |(1051727587/2000000000 : ℝ)|=(1051727587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-444893503/2000000000 : ℝ)|^2091 ≤ (13663447625203/100000000000000 : ℝ)^1579
        have hw : |(-444893503/2000000000 : ℝ)|=(444893503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (54502297/125000000 : ℝ)*x 0 + (527564233/1250000000 : ℝ)*x 1 + (281526333/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54502297/125000000 : ℝ)^2091 ≤ (520513665989/1562500000000 : ℝ)^1579 := by
    have hnat : (54502297 : ℕ)^2091*1562500000000^1579 ≤ 520513665989^1579*125000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54502297 125000000 520513665989 1562500000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527564233/1250000000 : ℝ)^2091 ≤ (31907137598249/100000000000000 : ℝ)^1579 := by
    have hnat : (527564233 : ℕ)^2091*100000000000000^1579 ≤ 31907137598249^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527564233 1250000000 31907137598249 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281526333/625000000 : ℝ)^2091 ≤ (17389993881351/50000000000000 : ℝ)^1579 := by
    have hnat : (281526333 : ℕ)^2091*50000000000000^1579 ≤ 17389993881351^1579*625000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281526333 625000000 17389993881351 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54502297/125000000 : ℝ), (527564233/1250000000 : ℝ), (281526333/625000000 : ℝ)] ![(520513665989/1562500000000 : ℝ), (31907137598249/100000000000000 : ℝ), (17389993881351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54502297/125000000 : ℝ)|^2091 ≤ (520513665989/1562500000000 : ℝ)^1579
        have hw : |(54502297/125000000 : ℝ)|=(54502297/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527564233/1250000000 : ℝ)|^2091 ≤ (31907137598249/100000000000000 : ℝ)^1579
        have hw : |(527564233/1250000000 : ℝ)|=(527564233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281526333/625000000 : ℝ)|^2091 ≤ (17389993881351/50000000000000 : ℝ)^1579
        have hw : |(281526333/625000000 : ℝ)|=(281526333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-430476813/2000000000 : ℝ)*x 0 + (1314759847/2500000000 : ℝ)*x 1 + (5400133459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430476813/2000000000 : ℝ)^2091 ≤ (408756918779/3125000000000 : ℝ)^1579 := by
    have hnat : (430476813 : ℕ)^2091*3125000000000^1579 ≤ 408756918779^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430476813 2000000000 408756918779 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314759847/2500000000 : ℝ)^2091 ≤ (10674528597067/25000000000000 : ℝ)^1579 := by
    have hnat : (1314759847 : ℕ)^2091*25000000000000^1579 ≤ 10674528597067^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314759847 2500000000 10674528597067 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400133459/10000000000 : ℝ)^2091 ≤ (552770802481/1250000000000 : ℝ)^1579 := by
    have hnat : (5400133459 : ℕ)^2091*1250000000000^1579 ≤ 552770802481^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400133459 10000000000 552770802481 1250000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430476813/2000000000 : ℝ), (1314759847/2500000000 : ℝ), (5400133459/10000000000 : ℝ)] ![(408756918779/3125000000000 : ℝ), (10674528597067/25000000000000 : ℝ), (552770802481/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430476813/2000000000 : ℝ)|^2091 ≤ (408756918779/3125000000000 : ℝ)^1579
        have hw : |(-430476813/2000000000 : ℝ)|=(430476813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314759847/2500000000 : ℝ)|^2091 ≤ (10674528597067/25000000000000 : ℝ)^1579
        have hw : |(1314759847/2500000000 : ℝ)|=(1314759847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400133459/10000000000 : ℝ)|^2091 ≤ (552770802481/1250000000000 : ℝ)^1579
        have hw : |(5400133459/10000000000 : ℝ)|=(5400133459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5310638429/10000000000 : ℝ)*x 0 + (-1041486343/5000000000 : ℝ)*x 1 + (5400133447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310638429/10000000000 : ℝ)^2091 ≤ (43253768559049/100000000000000 : ℝ)^1579 := by
    have hnat : (5310638429 : ℕ)^2091*100000000000000^1579 ≤ 43253768559049^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310638429 10000000000 43253768559049 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041486343/5000000000 : ℝ)^2091 ≤ (391392730209/3125000000000 : ℝ)^1579 := by
    have hnat : (1041486343 : ℕ)^2091*3125000000000^1579 ≤ 391392730209^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041486343 5000000000 391392730209 3125000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400133447/10000000000 : ℝ)^2091 ≤ (44221664068349/100000000000000 : ℝ)^1579 := by
    have hnat : (5400133447 : ℕ)^2091*100000000000000^1579 ≤ 44221664068349^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400133447 10000000000 44221664068349 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310638429/10000000000 : ℝ), (-1041486343/5000000000 : ℝ), (5400133447/10000000000 : ℝ)] ![(43253768559049/100000000000000 : ℝ), (391392730209/3125000000000 : ℝ), (44221664068349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310638429/10000000000 : ℝ)|^2091 ≤ (43253768559049/100000000000000 : ℝ)^1579
        have hw : |(5310638429/10000000000 : ℝ)|=(5310638429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041486343/5000000000 : ℝ)|^2091 ≤ (391392730209/3125000000000 : ℝ)^1579
        have hw : |(-1041486343/5000000000 : ℝ)|=(1041486343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400133447/10000000000 : ℝ)|^2091 ≤ (44221664068349/100000000000000 : ℝ)^1579
        have hw : |(5400133447/10000000000 : ℝ)|=(5400133447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531063837/1000000000 : ℝ)*x 0 + (84377091/156250000 : ℝ)*x 1 + (-2082972251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531063837/1000000000 : ℝ)^2091 ≤ (43253767922691/100000000000000 : ℝ)^1579 := by
    have hnat : (531063837 : ℕ)^2091*100000000000000^1579 ≤ 43253767922691^1579*1000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531063837 1000000000 43253767922691 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84377091/156250000 : ℝ)^2091 ≤ (44221668156659/100000000000000 : ℝ)^1579 := by
    have hnat : (84377091 : ℕ)^2091*100000000000000^1579 ≤ 44221668156659^1579*156250000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84377091 156250000 44221668156659 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082972251/10000000000 : ℝ)^2091 ≤ (3131140975747/25000000000000 : ℝ)^1579 := by
    have hnat : (2082972251 : ℕ)^2091*25000000000000^1579 ≤ 3131140975747^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082972251 10000000000 3131140975747 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531063837/1000000000 : ℝ), (84377091/156250000 : ℝ), (-2082972251/10000000000 : ℝ)] ![(43253767922691/100000000000000 : ℝ), (44221668156659/100000000000000 : ℝ), (3131140975747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531063837/1000000000 : ℝ)|^2091 ≤ (43253767922691/100000000000000 : ℝ)^1579
        have hw : |(531063837/1000000000 : ℝ)|=(531063837/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84377091/156250000 : ℝ)|^2091 ≤ (44221668156659/100000000000000 : ℝ)^1579
        have hw : |(84377091/156250000 : ℝ)|=(84377091/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2082972251/10000000000 : ℝ)|^2091 ≤ (3131140975747/25000000000000 : ℝ)^1579
        have hw : |(-2082972251/10000000000 : ℝ)|=(2082972251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s4_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180099017/5000000000 : ℝ)*x 0 + (1125904951/2500000000 : ℝ)*x 1 + (844263603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180099017/5000000000 : ℝ)^2091 ≤ (6662603808513/20000000000000 : ℝ)^1579 := by
    have hnat : (2180099017 : ℕ)^2091*20000000000000^1579 ≤ 6662603808513^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180099017 5000000000 6662603808513 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125904951/2500000000 : ℝ)^2091 ≤ (34771792435027/100000000000000 : ℝ)^1579 := by
    have hnat : (1125904951 : ℕ)^2091*100000000000000^1579 ≤ 34771792435027^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125904951 2500000000 34771792435027 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844263603/2000000000 : ℝ)^2091 ≤ (15957594258447/50000000000000 : ℝ)^1579 := by
    have hnat : (844263603 : ℕ)^2091*50000000000000^1579 ≤ 15957594258447^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844263603 2000000000 15957594258447 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180099017/5000000000 : ℝ), (1125904951/2500000000 : ℝ), (844263603/2000000000 : ℝ)] ![(6662603808513/20000000000000 : ℝ), (34771792435027/100000000000000 : ℝ), (15957594258447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180099017/5000000000 : ℝ)|^2091 ≤ (6662603808513/20000000000000 : ℝ)^1579
        have hw : |(2180099017/5000000000 : ℝ)|=(2180099017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125904951/2500000000 : ℝ)|^2091 ≤ (34771792435027/100000000000000 : ℝ)^1579
        have hw : |(1125904951/2500000000 : ℝ)|=(1125904951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(844263603/2000000000 : ℝ)|^2091 ≤ (15957594258447/50000000000000 : ℝ)^1579
        have hw : |(844263603/2000000000 : ℝ)|=(844263603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11229/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10719/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10719/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10719/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10719/100000 : ℝ) ^ (8363/2048 : ℝ) ≤ (10955665245953363/100000000000000000000 : ℝ) := by
    have hpowers : (10719/100000 : ℝ)^8363 ≤ (10955665245953363/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10719 : ℕ)^8363*100000000000000000000^2048 ≤ 10955665245953363^2048*100000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10719 100000 10955665245953363 100000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10719/100000 : ℝ)) (X := (10955665245953363/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (8363/2048 : ℝ) ≤ (8117805048999719/20000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^8363 ≤ (8117805048999719/20000000000000000000 : ℝ)^2048 := by
      have hnat : (3693 : ℕ)^8363*20000000000000000000^2048 ≤ 8117805048999719^2048*25000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 8117805048999719 20000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (8117805048999719/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010955665245953363/50000000000000000000 : ℝ) ≤ (10000536538239567/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (50010955665245953363/50000000000000000000 : ℝ)^2048 ≤ (10000536538239567/10000000000000000 : ℝ)^8363 := by
      have hnat : (50010955665245953363 : ℕ)^2048*10000000000000000^8363 ≤ 10000536538239567^8363*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010955665245953363 50000000000000000000 10000536538239567 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536538239567/10000000000000000 : ℝ)) (X := (50010955665245953363/50000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025772345245475979/50000000000000000000 : ℝ) ≤ (10001262023061083/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (50025772345245475979/50000000000000000000 : ℝ)^2048 ≤ (10001262023061083/10000000000000000 : ℝ)^8363 := by
      have hnat : (50025772345245475979 : ℕ)^2048*10000000000000000^8363 ≤ 10001262023061083^8363*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025772345245475979 50000000000000000000 10001262023061083 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001262023061083/10000000000000000 : ℝ)) (X := (50025772345245475979/50000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008117805048999719/10000000000000000000 : ℝ) ≤ (10001987507882599/10000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (10008117805048999719/10000000000000000000 : ℝ)^2048 ≤ (10001987507882599/10000000000000000 : ℝ)^8363 := by
      have hnat : (10008117805048999719 : ℕ)^2048*10000000000000000^8363 ≤ 10001987507882599^8363*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008117805048999719 10000000000000000000 10001987507882599 10000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001987507882599/10000000000000000 : ℝ)) (X := (10008117805048999719/10000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10955665245953363/100000000000000000000 : ℝ) ≤ ((1929362935518157383/1930000000000000000 : ℝ)+2*(25910172197/14475000000000 : ℝ)*(10719/100000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (1929362935518157383/1930000000000000000 : ℝ)+2*(25910172197/14475000000000 : ℝ)*(10719/100000 : ℝ)=(10000536538239567/10000000000000000 : ℝ) by norm_num, show 1+2*(10955665245953363/100000000000000000000 : ℝ)=(50010955665245953363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8117805048999719/20000000000000000000 : ℝ)+(10955665245953363/100000000000000000000 : ℝ) ≤ ((1929362935518157383/1930000000000000000 : ℝ)+(25910172197/14475000000000 : ℝ)*((3693/25000 : ℝ)+(10719/100000 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (1929362935518157383/1930000000000000000 : ℝ)+(25910172197/14475000000000 : ℝ)*((3693/25000 : ℝ)+(10719/100000 : ℝ))=(10001262023061083/10000000000000000 : ℝ) by norm_num, show 1+(8117805048999719/20000000000000000000 : ℝ)+(10955665245953363/100000000000000000000 : ℝ)=(50025772345245475979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8117805048999719/20000000000000000000 : ℝ) ≤ ((1929362935518157383/1930000000000000000 : ℝ)+2*(25910172197/14475000000000 : ℝ)*(3693/25000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (1929362935518157383/1930000000000000000 : ℝ)+2*(25910172197/14475000000000 : ℝ)*(3693/25000 : ℝ)=(10001987507882599/10000000000000000 : ℝ) by norm_num, show 1+2*(8117805048999719/20000000000000000000 : ℝ)=(10008117805048999719/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1929362935518157383/1930000000000000000 : ℝ)*(X 1 0+X 2 0)+(25910172197/14475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (1929362935518157383/1930000000000000000 : ℝ)) (alpha := (25910172197/14475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1929362935518157383/1930000000000000000 : ℝ)*(X 0 1+X 2 1)+(25910172197/14475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (1929362935518157383/1930000000000000000 : ℝ)) (alpha := (25910172197/14475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1929362935518157383/1930000000000000000 : ℝ)*(X 0 2+X 1 2)+(25910172197/14475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (10719/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (1929362935518157383/1930000000000000000 : ℝ)) (alpha := (25910172197/14475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430475379/2000000000 : ℝ)*X 0 0+(337533473/625000000 : ℝ)*X 0 1+(5258639169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346663577/10000000000 : ℝ)*X 1 0+(-278058379/1250000000 : ℝ)*X 1 1+(5258638469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83541621/156250000 : ℝ)*X 2 0+(1051727587/2000000000 : ℝ)*X 2 1+(-444893503/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((54502297/125000000 : ℝ)*X 0 0+(527564233/1250000000 : ℝ)*X 0 1+(281526333/625000000 : ℝ)*X 0 2+(54502297/125000000 : ℝ)*X 1 0+(527564233/1250000000 : ℝ)*X 1 1+(281526333/625000000 : ℝ)*X 1 2+(54502297/125000000 : ℝ)*X 2 0+(527564233/1250000000 : ℝ)*X 2 1+(281526333/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-430476813/2000000000 : ℝ)*X 0 0+(1314759847/2500000000 : ℝ)*X 0 1+(5400133459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310638429/10000000000 : ℝ)*X 1 0+(-1041486343/5000000000 : ℝ)*X 1 1+(5400133447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531063837/1000000000 : ℝ)*X 2 0+(84377091/156250000 : ℝ)*X 2 1+(-2082972251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180099017/5000000000 : ℝ)*X 0 0+(1125904951/2500000000 : ℝ)*X 0 1+(844263603/2000000000 : ℝ)*X 0 2+(2180099017/5000000000 : ℝ)*X 1 0+(1125904951/2500000000 : ℝ)*X 1 1+(844263603/2000000000 : ℝ)*X 1 2+(2180099017/5000000000 : ℝ)*X 2 0+(1125904951/2500000000 : ℝ)*X 2 1+(844263603/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (982227431887162257456527851/96500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117742471/10000000000000 : ℝ)*(base19) + (1807111421/100000000000000 : ℝ)*(base23) + (125885557/50000000000000 : ℝ)*(lower4) + (53202067/100000000000000 : ℝ)*(lower5) + (2642428619014633/50000000000000 : ℝ)*(major0) + (2642428619014633/50000000000000 : ℝ)*(major1) + (5284857238029267/100000000000000 : ℝ)*(major2) + (220231471869779/3125000000000 : ℝ)*(sp0) + (7047410512049677/100000000000000 : ℝ)*(sp1) + (1761850195072373/25000000000000 : ℝ)*(sp2) + (1761144360468941/50000000000000 : ℝ)*(sp3) + (4589641459/100000000000000 : ℝ)*(sp4) + (364082939/4000000000000 : ℝ)*(sp6) + (13726362161/100000000000000 : ℝ)*(sp7) + (880575611825011/25000000000000 : ℝ)*(f.failure) + (7047411689474387/100000000000000 : ℝ)*(f.sum) + (20211486248897/2895000000000000000000000000 : ℝ)*base65 + (1041883098811414561/96500000000000000000000000000000 : ℝ)*base68 + (12335232902463184783/579000000000000000000000000000000 : ℝ)*base69 + (1393133423238914561/96500000000000000000000000000000 : ℝ)*base72 + (837133134029/1447500000000000000000000000 : ℝ)*base74 + (21937953113463184783/579000000000000000000000000000000 : ℝ)*base75 + (1858246913581643683/289500000000000000000000000000000 : ℝ)*base78 + (2776871487778356317/289500000000000000000000000000000 : ℝ)*base79 + (4546699488869/1447500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (379791/312500000000000000000 : ℝ)*base89 + (379791/312500000000000000000 : ℝ)*base91 + (2745209/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144343172699740202100987911/24125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6822489/20000000000000 : ℝ)*(base19) + (54562239/50000000000000 : ℝ)*(lower2) + (7186291/100000000000000 : ℝ)*(upper3) + (88125203/100000000000000 : ℝ)*(lower4) + (246342557/100000000000000 : ℝ)*(upper5) + (2657452788110939/50000000000000 : ℝ)*(major0) + (2657452788110939/50000000000000 : ℝ)*(major1) + (5314905576221879/100000000000000 : ℝ)*(major2) + (1550973907/12500000000000 : ℝ)*(sp2) + (1556107247/12500000000000 : ℝ)*(sp3) + (1771870400114551/25000000000000 : ℝ)*(sp4) + (44296759789661/625000000000 : ℝ)*(sp5) + (1771867298166737/25000000000000 : ℝ)*(sp6) + (1771158451844837/50000000000000 : ℝ)*(sp7) + (70846587050953/2000000000000 : ℝ)*(f.failure) + (1771870400114551/25000000000000 : ℝ)*(f.sum) + (2259213600177/482500000000000000000000000 : ℝ)*base66 + (4632010731693662089/289500000000000000000000000000000 : ℝ)*base68 + (4358392142890347971/579000000000000000000000000000000 : ℝ)*base69 + (4580294279151662089/289500000000000000000000000000000 : ℝ)*base72 + (720069314543/482500000000000000000000000 : ℝ)*base73 + (2005505178745652029/579000000000000000000000000000000 : ℝ)*base76 + (8087791203859062089/289500000000000000000000000000000 : ℝ)*base78 + (5604356207353062089/289500000000000000000000000000000 : ℝ)*base80 + (11850446499443/1447500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (46893/25000000000000000000 : ℝ)*base89 + (46893/25000000000000000000 : ℝ)*base91 + (203107/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1171_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10719/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1171_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1171_s5_0 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-538238329/2500000000 : ℝ)*x 0 + (269708117/500000000 : ℝ)*x 1 + (5264633839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538238329/2500000000 : ℝ)^2091 ≤ (13084802710639/100000000000000 : ℝ)^1579 := by
    have hnat : (538238329 : ℕ)^2091*100000000000000^1579 ≤ 13084802710639^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538238329 2500000000 13084802710639 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269708117/500000000 : ℝ)^2091 ≤ (22078461529727/50000000000000 : ℝ)^1579 := by
    have hnat : (269708117 : ℕ)^2091*50000000000000^1579 ≤ 22078461529727^1579*500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269708117 500000000 22078461529727 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264633839/10000000000 : ℝ)^2091 ≤ (10689568552047/25000000000000 : ℝ)^1579 := by
    have hnat : (5264633839 : ℕ)^2091*25000000000000^1579 ≤ 10689568552047^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264633839 10000000000 10689568552047 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538238329/2500000000 : ℝ), (269708117/500000000 : ℝ), (5264633839/10000000000 : ℝ)] ![(13084802710639/100000000000000 : ℝ), (22078461529727/50000000000000 : ℝ), (10689568552047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538238329/2500000000 : ℝ)|^2091 ≤ (13084802710639/100000000000000 : ℝ)^1579
        have hw : |(-538238329/2500000000 : ℝ)|=(538238329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269708117/500000000 : ℝ)|^2091 ≤ (22078461529727/50000000000000 : ℝ)^1579
        have hw : |(269708117/500000000 : ℝ)|=(269708117/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264633839/10000000000 : ℝ)|^2091 ≤ (10689568552047/25000000000000 : ℝ)^1579
        have hw : |(5264633839/10000000000 : ℝ)|=(5264633839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_1 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345060663/10000000000 : ℝ)*x 0 + (-277333579/1250000000 : ℝ)*x 1 + (5264633823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345060663/10000000000 : ℝ)^2091 ≤ (10906356676773/25000000000000 : ℝ)^1579 := by
    have hnat : (5345060663 : ℕ)^2091*25000000000000^1579 ≤ 10906356676773^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345060663 10000000000 10906356676773 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (277333579/1250000000 : ℝ)^2091 ≤ (13616299244851/100000000000000 : ℝ)^1579 := by
    have hnat : (277333579 : ℕ)^2091*100000000000000^1579 ≤ 13616299244851^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277333579 1250000000 13616299244851 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264633823/10000000000 : ℝ)^2091 ≤ (42758274036103/100000000000000 : ℝ)^1579 := by
    have hnat : (5264633823 : ℕ)^2091*100000000000000^1579 ≤ 42758274036103^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264633823 10000000000 42758274036103 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345060663/10000000000 : ℝ), (-277333579/1250000000 : ℝ), (5264633823/10000000000 : ℝ)] ![(10906356676773/25000000000000 : ℝ), (13616299244851/100000000000000 : ℝ), (42758274036103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345060663/10000000000 : ℝ)|^2091 ≤ (10906356676773/25000000000000 : ℝ)^1579
        have hw : |(5345060663/10000000000 : ℝ)|=(5345060663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-277333579/1250000000 : ℝ)|^2091 ≤ (13616299244851/100000000000000 : ℝ)^1579
        have hw : |(-277333579/1250000000 : ℝ)|=(277333579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264633823/10000000000 : ℝ)|^2091 ≤ (42758274036103/100000000000000 : ℝ)^1579
        have hw : |(5264633823/10000000000 : ℝ)|=(5264633823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_2 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336265171/2500000000 : ℝ)*x 0 + (5264633807/10000000000 : ℝ)*x 1 + (-17749349/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336265171/2500000000 : ℝ)^2091 ≤ (43625426934067/100000000000000 : ℝ)^1579 := by
    have hnat : (1336265171 : ℕ)^2091*100000000000000^1579 ≤ 43625426934067^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336265171 2500000000 43625426934067 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264633807/10000000000 : ℝ)^2091 ≤ (42758273864017/100000000000000 : ℝ)^1579 := by
    have hnat : (5264633807 : ℕ)^2091*100000000000000^1579 ≤ 42758273864017^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264633807 10000000000 42758273864017 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17749349/80000000 : ℝ)^2091 ≤ (13616299187961/100000000000000 : ℝ)^1579 := by
    have hnat : (17749349 : ℕ)^2091*100000000000000^1579 ≤ 13616299187961^1579*80000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17749349 80000000 13616299187961 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336265171/2500000000 : ℝ), (5264633807/10000000000 : ℝ), (-17749349/80000000 : ℝ)] ![(43625426934067/100000000000000 : ℝ), (42758273864017/100000000000000 : ℝ), (13616299187961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336265171/2500000000 : ℝ)|^2091 ≤ (43625426934067/100000000000000 : ℝ)^1579
        have hw : |(1336265171/2500000000 : ℝ)|=(1336265171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264633807/10000000000 : ℝ)|^2091 ≤ (42758273864017/100000000000000 : ℝ)^1579
        have hw : |(5264633807/10000000000 : ℝ)|=(5264633807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17749349/80000000 : ℝ)|^2091 ≤ (13616299187961/100000000000000 : ℝ)^1579
        have hw : |(-17749349/80000000 : ℝ)|=(17749349/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_3 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180260491/5000000000 : ℝ)*x 0 + (1058210943/2500000000 : ℝ)*x 1 + (224600201/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180260491/5000000000 : ℝ)^2091 ≤ (16658143278427/50000000000000 : ℝ)^1579 := by
    have hnat : (2180260491 : ℕ)^2091*50000000000000^1579 ≤ 16658143278427^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180260491 5000000000 16658143278427 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058210943/2500000000 : ℝ)^2091 ≤ (32030635554389/100000000000000 : ℝ)^1579 := by
    have hnat : (1058210943 : ℕ)^2091*100000000000000^1579 ≤ 32030635554389^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058210943 2500000000 32030635554389 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224600201/500000000 : ℝ)^2091 ≤ (433163473259/1250000000000 : ℝ)^1579 := by
    have hnat : (224600201 : ℕ)^2091*1250000000000^1579 ≤ 433163473259^1579*500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224600201 500000000 433163473259 1250000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180260491/5000000000 : ℝ), (1058210943/2500000000 : ℝ), (224600201/500000000 : ℝ)] ![(16658143278427/50000000000000 : ℝ), (32030635554389/100000000000000 : ℝ), (433163473259/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180260491/5000000000 : ℝ)|^2091 ≤ (16658143278427/50000000000000 : ℝ)^1579
        have hw : |(2180260491/5000000000 : ℝ)|=(2180260491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058210943/2500000000 : ℝ)|^2091 ≤ (32030635554389/100000000000000 : ℝ)^1579
        have hw : |(1058210943/2500000000 : ℝ)|=(1058210943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224600201/500000000 : ℝ)|^2091 ≤ (433163473259/1250000000000 : ℝ)^1579
        have hw : |(224600201/500000000 : ℝ)|=(224600201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_4 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-538239641/2500000000 : ℝ)*x 0 + (2632483927/5000000000 : ℝ)*x 1 + (1078765409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538239641/2500000000 : ℝ)^2091 ≤ (2616968989633/20000000000000 : ℝ)^1579 := by
    have hnat : (538239641 : ℕ)^2091*20000000000000^1579 ≤ 2616968989633^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538239641 2500000000 2616968989633 20000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632483927/5000000000 : ℝ)^2091 ≤ (10690466672003/25000000000000 : ℝ)^1579 := by
    have hnat : (2632483927 : ℕ)^2091*25000000000000^1579 ≤ 10690466672003^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632483927 5000000000 10690466672003 25000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078765409/2000000000 : ℝ)^2091 ≤ (44153288352567/100000000000000 : ℝ)^1579 := by
    have hnat : (1078765409 : ℕ)^2091*100000000000000^1579 ≤ 44153288352567^1579*2000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078765409 2000000000 44153288352567 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538239641/2500000000 : ℝ), (2632483927/5000000000 : ℝ), (1078765409/2000000000 : ℝ)] ![(2616968989633/20000000000000 : ℝ), (10690466672003/25000000000000 : ℝ), (44153288352567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538239641/2500000000 : ℝ)|^2091 ≤ (2616968989633/20000000000000 : ℝ)^1579
        have hw : |(-538239641/2500000000 : ℝ)|=(538239641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632483927/5000000000 : ℝ)|^2091 ≤ (10690466672003/25000000000000 : ℝ)^1579
        have hw : |(2632483927/5000000000 : ℝ)|=(2632483927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078765409/2000000000 : ℝ)|^2091 ≤ (44153288352567/100000000000000 : ℝ)^1579
        have hw : |(1078765409/2000000000 : ℝ)|=(1078765409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_5 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (21248699/40000000 : ℝ)*x 0 + (-522368861/2500000000 : ℝ)*x 1 + (2696913523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21248699/40000000 : ℝ)^2091 ≤ (43270339663533/100000000000000 : ℝ)^1579 := by
    have hnat : (21248699 : ℕ)^2091*100000000000000^1579 ≤ 43270339663533^1579*40000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21248699 40000000 43270339663533 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522368861/2500000000 : ℝ)^2091 ≤ (251527439173/2000000000000 : ℝ)^1579 := by
    have hnat : (522368861 : ℕ)^2091*2000000000000^1579 ≤ 251527439173^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522368861 2500000000 251527439173 2000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696913523/5000000000 : ℝ)^2091 ≤ (44153288363407/100000000000000 : ℝ)^1579 := by
    have hnat : (2696913523 : ℕ)^2091*100000000000000^1579 ≤ 44153288363407^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696913523 5000000000 44153288363407 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21248699/40000000 : ℝ), (-522368861/2500000000 : ℝ), (2696913523/5000000000 : ℝ)] ![(43270339663533/100000000000000 : ℝ), (251527439173/2000000000000 : ℝ), (44153288363407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21248699/40000000 : ℝ)|^2091 ≤ (43270339663533/100000000000000 : ℝ)^1579
        have hw : |(21248699/40000000 : ℝ)|=(21248699/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522368861/2500000000 : ℝ)|^2091 ≤ (251527439173/2000000000000 : ℝ)^1579
        have hw : |(-522368861/2500000000 : ℝ)|=(522368861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696913523/5000000000 : ℝ)|^2091 ≤ (44153288363407/100000000000000 : ℝ)^1579
        have hw : |(2696913523/5000000000 : ℝ)|=(2696913523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_6 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312174749/10000000000 : ℝ)*x 0 + (5393827047/10000000000 : ℝ)*x 1 + (-522368861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312174749/10000000000 : ℝ)^2091 ≤ (21635169826373/50000000000000 : ℝ)^1579 := by
    have hnat : (5312174749 : ℕ)^2091*50000000000000^1579 ≤ 21635169826373^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312174749 10000000000 21635169826373 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393827047/10000000000 : ℝ)^2091 ≤ (5519161046781/12500000000000 : ℝ)^1579 := by
    have hnat : (5393827047 : ℕ)^2091*12500000000000^1579 ≤ 5519161046781^1579*10000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393827047 10000000000 5519161046781 12500000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522368861/2500000000 : ℝ)^2091 ≤ (251527439173/2000000000000 : ℝ)^1579 := by
    have hnat : (522368861 : ℕ)^2091*2000000000000^1579 ≤ 251527439173^1579*2500000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522368861 2500000000 251527439173 2000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312174749/10000000000 : ℝ), (5393827047/10000000000 : ℝ), (-522368861/2500000000 : ℝ)] ![(21635169826373/50000000000000 : ℝ), (5519161046781/12500000000000 : ℝ), (251527439173/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312174749/10000000000 : ℝ)|^2091 ≤ (21635169826373/50000000000000 : ℝ)^1579
        have hw : |(5312174749/10000000000 : ℝ)|=(5312174749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393827047/10000000000 : ℝ)|^2091 ≤ (5519161046781/12500000000000 : ℝ)^1579
        have hw : |(5393827047/10000000000 : ℝ)|=(5393827047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522368861/2500000000 : ℝ)|^2091 ≤ (251527439173/2000000000000 : ℝ)^1579
        have hw : |(-522368861/2500000000 : ℝ)|=(522368861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1171_s5_7 (p : ℝ) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2180265707/5000000000 : ℝ)*x 0 + (561416957/1250000000 : ℝ)*x 1 + (169340583/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180265707/5000000000 : ℝ)^2091 ≤ (16658196053381/50000000000000 : ℝ)^1579 := by
    have hnat : (2180265707 : ℕ)^2091*50000000000000^1579 ≤ 16658196053381^1579*5000000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180265707 5000000000 16658196053381 50000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561416957/1250000000 : ℝ)^2091 ≤ (270673829169/781250000000 : ℝ)^1579 := by
    have hnat : (561416957 : ℕ)^2091*781250000000^1579 ≤ 270673829169^1579*1250000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561416957 1250000000 270673829169 781250000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169340583/400000000 : ℝ)^2091 ≤ (32037357753521/100000000000000 : ℝ)^1579 := by
    have hnat : (169340583 : ℕ)^2091*100000000000000^1579 ≤ 32037357753521^1579*400000000^2091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169340583 400000000 32037357753521 100000000000000 2091 1579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2091/512 : ℝ)) 2091 1579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180265707/5000000000 : ℝ), (561416957/1250000000 : ℝ), (169340583/400000000 : ℝ)] ![(16658196053381/50000000000000 : ℝ), (270673829169/781250000000 : ℝ), (32037357753521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180265707/5000000000 : ℝ)|^2091 ≤ (16658196053381/50000000000000 : ℝ)^1579
        have hw : |(2180265707/5000000000 : ℝ)|=(2180265707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561416957/1250000000 : ℝ)|^2091 ≤ (270673829169/781250000000 : ℝ)^1579
        have hw : |(561416957/1250000000 : ℝ)|=(561416957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169340583/400000000 : ℝ)|^2091 ≤ (32037357753521/100000000000000 : ℝ)^1579
        have hw : |(169340583/400000000 : ℝ)|=(169340583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1171_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14101/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11229/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11229/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11229/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11229/100000 : ℝ) ^ (8363/2048 : ℝ) ≤ (3311399096446603/25000000000000000000 : ℝ) := by
    have hpowers : (11229/100000 : ℝ)^8363 ≤ (3311399096446603/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11229 : ℕ)^8363*25000000000000000000^2048 ≤ 3311399096446603^2048*100000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11229 100000 3311399096446603 25000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11229/100000 : ℝ)) (X := (3311399096446603/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (8363/2048 : ℝ) ≤ (6976602033739881/20000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^8363 ≤ (6976602033739881/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7117 : ℕ)^8363*20000000000000000000^2048 ≤ 6976602033739881^2048*50000^8363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 6976602033739881 20000000000000000000 8363 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (6976602033739881/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503311399096446603/12500000000000000000 : ℝ) ≤ (5000324336584997/5000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (12503311399096446603/12500000000000000000 : ℝ)^2048 ≤ (5000324336584997/5000000000000000 : ℝ)^8363 := by
      have hnat : (12503311399096446603 : ℕ)^2048*5000000000000000^8363 ≤ 5000324336584997^8363*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503311399096446603 12500000000000000000 5000324336584997 5000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000324336584997/5000000000000000 : ℝ)) (X := (12503311399096446603/12500000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048128606554485817/100000000000000000000 : ℝ) ≤ (5000589199332473/5000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (100048128606554485817/100000000000000000000 : ℝ)^2048 ≤ (5000589199332473/5000000000000000 : ℝ)^8363 := by
      have hnat : (100048128606554485817 : ℕ)^2048*5000000000000000^8363 ≤ 5000589199332473^8363*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048128606554485817 100000000000000000000 5000589199332473 5000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000589199332473/5000000000000000 : ℝ)) (X := (100048128606554485817/100000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006976602033739881/10000000000000000000 : ℝ) ≤ (5000854062079949/5000000000000000 : ℝ) ^ (8363/2048 : ℝ) := by
    have hpowers : (10006976602033739881/10000000000000000000 : ℝ)^2048 ≤ (5000854062079949/5000000000000000 : ℝ)^8363 := by
      have hnat : (10006976602033739881 : ℕ)^2048*5000000000000000^8363 ≤ 5000854062079949^8363*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006976602033739881 10000000000000000000 5000854062079949 5000000000000000 2048 8363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000854062079949/5000000000000000 : ℝ)) (X := (10006976602033739881/10000000000000000000 : ℝ)) (by norm_num) 8363 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3311399096446603/25000000000000000000 : ℝ) ≤ ((15020026343855099977/15025000000000000000 : ℝ)+2*(66215686869/37562500000000 : ℝ)*(11229/100000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (15020026343855099977/15025000000000000000 : ℝ)+2*(66215686869/37562500000000 : ℝ)*(11229/100000 : ℝ)=(5000324336584997/5000000000000000 : ℝ) by norm_num, show 1+2*(3311399096446603/25000000000000000000 : ℝ)=(12503311399096446603/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6976602033739881/20000000000000000000 : ℝ)+(3311399096446603/25000000000000000000 : ℝ) ≤ ((15020026343855099977/15025000000000000000 : ℝ)+(66215686869/37562500000000 : ℝ)*((7117/50000 : ℝ)+(11229/100000 : ℝ)))^(8363/2048 : ℝ) := by
    rw [show (15020026343855099977/15025000000000000000 : ℝ)+(66215686869/37562500000000 : ℝ)*((7117/50000 : ℝ)+(11229/100000 : ℝ))=(5000589199332473/5000000000000000 : ℝ) by norm_num, show 1+(6976602033739881/20000000000000000000 : ℝ)+(3311399096446603/25000000000000000000 : ℝ)=(100048128606554485817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6976602033739881/20000000000000000000 : ℝ) ≤ ((15020026343855099977/15025000000000000000 : ℝ)+2*(66215686869/37562500000000 : ℝ)*(7117/50000 : ℝ))^(8363/2048 : ℝ) := by
    rw [show (15020026343855099977/15025000000000000000 : ℝ)+2*(66215686869/37562500000000 : ℝ)*(7117/50000 : ℝ)=(5000854062079949/5000000000000000 : ℝ) by norm_num, show 1+2*(6976602033739881/20000000000000000000 : ℝ)=(10006976602033739881/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15020026343855099977/15025000000000000000 : ℝ)*(X 1 0+X 2 0)+(66215686869/37562500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (15020026343855099977/15025000000000000000 : ℝ)) (alpha := (66215686869/37562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15020026343855099977/15025000000000000000 : ℝ)*(X 0 1+X 2 1)+(66215686869/37562500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (15020026343855099977/15025000000000000000 : ℝ)) (alpha := (66215686869/37562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15020026343855099977/15025000000000000000 : ℝ)*(X 0 2+X 1 2)+(66215686869/37562500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8363/2048 : ℝ)) (lo := (11229/100000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (15020026343855099977/15025000000000000000 : ℝ)) (alpha := (66215686869/37562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-538238329/2500000000 : ℝ)*X 0 0+(269708117/500000000 : ℝ)*X 0 1+(5264633839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345060663/10000000000 : ℝ)*X 1 0+(-277333579/1250000000 : ℝ)*X 1 1+(5264633823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336265171/2500000000 : ℝ)*X 2 0+(5264633807/10000000000 : ℝ)*X 2 1+(-17749349/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180260491/5000000000 : ℝ)*X 0 0+(1058210943/2500000000 : ℝ)*X 0 1+(224600201/500000000 : ℝ)*X 0 2+(2180260491/5000000000 : ℝ)*X 1 0+(1058210943/2500000000 : ℝ)*X 1 1+(224600201/500000000 : ℝ)*X 1 2+(2180260491/5000000000 : ℝ)*X 2 0+(1058210943/2500000000 : ℝ)*X 2 1+(224600201/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-538239641/2500000000 : ℝ)*X 0 0+(2632483927/5000000000 : ℝ)*X 0 1+(1078765409/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21248699/40000000 : ℝ)*X 1 0+(-522368861/2500000000 : ℝ)*X 1 1+(2696913523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312174749/10000000000 : ℝ)*X 2 0+(5393827047/10000000000 : ℝ)*X 2 1+(-522368861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180265707/5000000000 : ℝ)*X 0 0+(561416957/1250000000 : ℝ)*X 0 1+(169340583/400000000 : ℝ)*X 0 2+(2180265707/5000000000 : ℝ)*X 1 0+(561416957/1250000000 : ℝ)*X 1 1+(169340583/400000000 : ℝ)*X 1 2+(2180265707/5000000000 : ℝ)*X 2 0+(561416957/1250000000 : ℝ)*X 2 1+(169340583/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1171_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5275996578138252742502487681/751250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (693300577/50000000000000 : ℝ)*(base19) + (634393833/50000000000000 : ℝ)*(base23) + (79184831/100000000000000 : ℝ)*(lower2) + (39662717/25000000000000 : ℝ)*(upper3) + (2043493/3125000000000 : ℝ)*(upper5) + (1447380128888813/25000000000000 : ℝ)*(major0) + (1447380128888813/25000000000000 : ℝ)*(major1) + (5789520515555253/100000000000000 : ℝ)*(major2) + (7720347930602377/100000000000000 : ℝ)*(sp0) + (1544076826268867/20000000000000 : ℝ)*(sp1) + (7720384249157823/100000000000000 : ℝ)*(sp2) + (192931720945259/5000000000000 : ℝ)*(sp3) + (37587343113/100000000000000 : ℝ)*(sp4) + (10430080627/50000000000000 : ℝ)*(sp7) + (1929327639533217/50000000000000 : ℝ)*(f.failure) + (7720385517945489/100000000000000 : ℝ)*(f.sum) + (585204973699/187812500000000000000000000 : ℝ)*base66 + (5657538979473692699/375625000000000000000000000000000 : ℝ)*base68 + (6967167633782729181/1502500000000000000000000000000000 : ℝ)*base69 + (1963729406820567699/375625000000000000000000000000000 : ℝ)*base72 + (2877433121061/751250000000000000000000000 : ℝ)*base74 + (21543646867490229181/1502500000000000000000000000000000 : ℝ)*base75 + (1787022246149342699/375625000000000000000000000000000 : ℝ)*base78 + (6980031446834967699/375625000000000000000000000000000 : ℝ)*base80 + (20081023468971/15025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8703877/625000000000000000000 : ℝ)*base89 + (8703877/625000000000000000000 : ℝ)*base91 + (2453877/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3516970290221915311908912453/375625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168897549/10000000000000 : ℝ)*(base19) + (1840923333/100000000000000 : ℝ)*(base23) + (93733137/50000000000000 : ℝ)*(upper3) + (34839871/50000000000000 : ℝ)*(lower4) + (189647757/100000000000000 : ℝ)*(upper5) + (5819532760787137/100000000000000 : ℝ)*(major0) + (5819532760787137/100000000000000 : ℝ)*(major1) + (5819532760787137/100000000000000 : ℝ)*(major2) + (9153438177/20000000000000 : ℝ)*(sp1) + (49359470179/100000000000000 : ℝ)*(sp2) + (388020354037209/5000000000000 : ℝ)*(sp4) + (1552071924915561/20000000000000 : ℝ)*(sp5) + (7760355880350669/100000000000000 : ℝ)*(sp6) + (1939329064365333/50000000000000 : ℝ)*(sp7) + (1939329064365333/50000000000000 : ℝ)*(f.failure) + (388020354037209/5000000000000 : ℝ)*(f.sum) + (5031418158169/3756250000000000000000000000 : ℝ)*base66 + (17765265854431795849/1502500000000000000000000000000000 : ℝ)*base67 + (10235907767653204151/1502500000000000000000000000000000 : ℝ)*base70 + (211850420899295849/1502500000000000000000000000000000 : ℝ)*base71 + (27679122628381/3756250000000000000000000000 : ℝ)*base73 + (3289192631634295849/1502500000000000000000000000000000 : ℝ)*base75 + (7103338605369295849/1502500000000000000000000000000000 : ℝ)*base77 + (11498494349991795849/1502500000000000000000000000000000 : ℝ)*base79 + (16993964328551/15025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8776327/625000000000000000000 : ℝ)*base90 + (8776327/625000000000000000000 : ℝ)*base92 + (8776327/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1171_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1171_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1171_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8209/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1171_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1171_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1171_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8363/2048 : ℝ) ≤ p) (hpb : p ≤ (2091/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18754981/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8209/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9199/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14101/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1171_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
