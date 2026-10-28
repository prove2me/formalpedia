-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:56:46.160792+00:00
-- url     : https://prove2.me/submissions/8192c8d6-aeed-4a08-81bc-e7e44fec3dc1

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
theorem support_rectangle_w1264_box_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-397372961/2000000000 : ℝ)*x 0 + (107490153/200000000 : ℝ)*x 1 + (5374507319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397372961/2000000000 : ℝ)^8457 ≤ (11854890829171/100000000000000 : ℝ)^6409 := by
    have hnat : (397372961 : ℕ)^8457*100000000000000^6409 ≤ 11854890829171^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397372961 2000000000 11854890829171 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107490153/200000000 : ℝ)^8457 ≤ (44072556368793/100000000000000 : ℝ)^6409 := by
    have hnat : (107490153 : ℕ)^8457*100000000000000^6409 ≤ 44072556368793^6409*200000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107490153 200000000 44072556368793 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374507319/10000000000 : ℝ)^8457 ≤ (44072552787139/100000000000000 : ℝ)^6409 := by
    have hnat : (5374507319 : ℕ)^8457*100000000000000^6409 ≤ 44072552787139^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374507319 10000000000 44072552787139 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397372961/2000000000 : ℝ), (107490153/200000000 : ℝ), (5374507319/10000000000 : ℝ)] ![(11854890829171/100000000000000 : ℝ), (44072556368793/100000000000000 : ℝ), (44072552787139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397372961/2000000000 : ℝ)|^8457 ≤ (11854890829171/100000000000000 : ℝ)^6409
        have hw : |(-397372961/2000000000 : ℝ)|=(397372961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107490153/200000000 : ℝ)|^8457 ≤ (44072556368793/100000000000000 : ℝ)^6409
        have hw : |(107490153/200000000 : ℝ)|=(107490153/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374507319/10000000000 : ℝ)|^8457 ≤ (44072552787139/100000000000000 : ℝ)^6409
        have hw : |(5374507319/10000000000 : ℝ)|=(5374507319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296941867/10000000000 : ℝ)*x 0 + (-130771059/625000000 : ℝ)*x 1 + (5374507653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296941867/10000000000 : ℝ)^8457 ≤ (2161759077877/5000000000000 : ℝ)^6409 := by
    have hnat : (5296941867 : ℕ)^8457*5000000000000^6409 ≤ 2161759077877^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296941867 10000000000 2161759077877 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130771059/625000000 : ℝ)^8457 ≤ (253845240511/2000000000000 : ℝ)^6409 := by
    have hnat : (130771059 : ℕ)^8457*2000000000000^6409 ≤ 253845240511^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130771059 625000000 253845240511 2000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374507653/10000000000 : ℝ)^8457 ≤ (8814511280251/20000000000000 : ℝ)^6409 := by
    have hnat : (5374507653 : ℕ)^8457*20000000000000^6409 ≤ 8814511280251^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374507653 10000000000 8814511280251 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296941867/10000000000 : ℝ), (-130771059/625000000 : ℝ), (5374507653/10000000000 : ℝ)] ![(2161759077877/5000000000000 : ℝ), (253845240511/2000000000000 : ℝ), (8814511280251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296941867/10000000000 : ℝ)|^8457 ≤ (2161759077877/5000000000000 : ℝ)^6409
        have hw : |(5296941867/10000000000 : ℝ)|=(5296941867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-130771059/625000000 : ℝ)|^8457 ≤ (253845240511/2000000000000 : ℝ)^6409
        have hw : |(-130771059/625000000 : ℝ)|=(130771059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374507653/10000000000 : ℝ)|^8457 ≤ (8814511280251/20000000000000 : ℝ)^6409
        have hw : |(5374507653/10000000000 : ℝ)|=(5374507653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296941823/10000000000 : ℝ)*x 0 + (1074901493/2000000000 : ℝ)*x 1 + (-2092337257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296941823/10000000000 : ℝ)^8457 ≤ (10808795270909/25000000000000 : ℝ)^6409 := by
    have hnat : (5296941823 : ℕ)^8457*25000000000000^6409 ≤ 10808795270909^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296941823 10000000000 10808795270909 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074901493/2000000000 : ℝ)^8457 ≤ (22036277183481/50000000000000 : ℝ)^6409 := by
    have hnat : (1074901493 : ℕ)^8457*50000000000000^6409 ≤ 22036277183481^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074901493 2000000000 22036277183481 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092337257/10000000000 : ℝ)^8457 ≤ (6346132265477/50000000000000 : ℝ)^6409 := by
    have hnat : (2092337257 : ℕ)^8457*50000000000000^6409 ≤ 6346132265477^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092337257 10000000000 6346132265477 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296941823/10000000000 : ℝ), (1074901493/2000000000 : ℝ), (-2092337257/10000000000 : ℝ)] ![(10808795270909/25000000000000 : ℝ), (22036277183481/50000000000000 : ℝ), (6346132265477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296941823/10000000000 : ℝ)|^8457 ≤ (10808795270909/25000000000000 : ℝ)^6409
        have hw : |(5296941823/10000000000 : ℝ)|=(5296941823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074901493/2000000000 : ℝ)|^8457 ≤ (22036277183481/50000000000000 : ℝ)^6409
        have hw : |(1074901493/2000000000 : ℝ)|=(1074901493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2092337257/10000000000 : ℝ)|^8457 ≤ (6346132265477/50000000000000 : ℝ)^6409
        have hw : |(-2092337257/10000000000 : ℝ)|=(2092337257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4454081819/10000000000 : ℝ)*x 0 + (107415929/250000000 : ℝ)*x 1 + (4296637037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4454081819/10000000000 : ℝ)^8457 ≤ (343968480861/1000000000000 : ℝ)^6409 := by
    have hnat : (4454081819 : ℕ)^8457*1000000000000^6409 ≤ 343968480861^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454081819 10000000000 343968480861 1000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107415929/250000000 : ℝ)^8457 ≤ (32801576571069/100000000000000 : ℝ)^6409 := by
    have hnat : (107415929 : ℕ)^8457*100000000000000^6409 ≤ 32801576571069^6409*250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107415929 250000000 32801576571069 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4296637037/10000000000 : ℝ)^8457 ≤ (6560315066399/20000000000000 : ℝ)^6409 := by
    have hnat : (4296637037 : ℕ)^8457*20000000000000^6409 ≤ 6560315066399^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296637037 10000000000 6560315066399 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4454081819/10000000000 : ℝ), (107415929/250000000 : ℝ), (4296637037/10000000000 : ℝ)] ![(343968480861/1000000000000 : ℝ), (32801576571069/100000000000000 : ℝ), (6560315066399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4454081819/10000000000 : ℝ)|^8457 ≤ (343968480861/1000000000000 : ℝ)^6409
        have hw : |(4454081819/10000000000 : ℝ)|=(4454081819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107415929/250000000 : ℝ)|^8457 ≤ (32801576571069/100000000000000 : ℝ)^6409
        have hw : |(107415929/250000000 : ℝ)|=(107415929/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4296637037/10000000000 : ℝ)|^8457 ≤ (6560315066399/20000000000000 : ℝ)^6409
        have hw : |(4296637037/10000000000 : ℝ)|=(4296637037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1117137141/5000000000 : ℝ)*x 0 + (5282503099/10000000000 : ℝ)*x 1 + (5282503197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117137141/5000000000 : ℝ)^8457 ≤ (2768105480399/20000000000000 : ℝ)^6409 := by
    have hnat : (1117137141 : ℕ)^8457*20000000000000^6409 ≤ 2768105480399^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117137141 5000000000 2768105480399 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282503099/10000000000 : ℝ)^8457 ≤ (10769933941151/25000000000000 : ℝ)^6409 := by
    have hnat : (5282503099 : ℕ)^8457*25000000000000^6409 ≤ 10769933941151^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282503099 10000000000 10769933941151 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282503197/10000000000 : ℝ)^8457 ≤ (21539868409599/50000000000000 : ℝ)^6409 := by
    have hnat : (5282503197 : ℕ)^8457*50000000000000^6409 ≤ 21539868409599^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282503197 10000000000 21539868409599 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1117137141/5000000000 : ℝ), (5282503099/10000000000 : ℝ), (5282503197/10000000000 : ℝ)] ![(2768105480399/20000000000000 : ℝ), (10769933941151/25000000000000 : ℝ), (21539868409599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1117137141/5000000000 : ℝ)|^8457 ≤ (2768105480399/20000000000000 : ℝ)^6409
        have hw : |(-1117137141/5000000000 : ℝ)|=(1117137141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282503099/10000000000 : ℝ)|^8457 ≤ (10769933941151/25000000000000 : ℝ)^6409
        have hw : |(5282503099/10000000000 : ℝ)|=(5282503099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282503197/10000000000 : ℝ)|^8457 ≤ (21539868409599/50000000000000 : ℝ)^6409
        have hw : |(5282503197/10000000000 : ℝ)|=(5282503197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335110467/625000000 : ℝ)*x 0 + (-266108921/1250000000 : ℝ)*x 1 + (8253911/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335110467/625000000 : ℝ)^8457 ≤ (43934750883479/100000000000000 : ℝ)^6409 := by
    have hnat : (335110467 : ℕ)^8457*100000000000000^6409 ≤ 43934750883479^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335110467 625000000 43934750883479 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266108921/1250000000 : ℝ)^8457 ≤ (12985513974549/100000000000000 : ℝ)^6409 := by
    have hnat : (266108921 : ℕ)^8457*100000000000000^6409 ≤ 12985513974549^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266108921 1250000000 12985513974549 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8253911/15625000 : ℝ)^8457 ≤ (8615947025939/20000000000000 : ℝ)^6409 := by
    have hnat : (8253911 : ℕ)^8457*20000000000000^6409 ≤ 8615947025939^6409*15625000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8253911 15625000 8615947025939 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335110467/625000000 : ℝ), (-266108921/1250000000 : ℝ), (8253911/15625000 : ℝ)] ![(43934750883479/100000000000000 : ℝ), (12985513974549/100000000000000 : ℝ), (8615947025939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335110467/625000000 : ℝ)|^8457 ≤ (43934750883479/100000000000000 : ℝ)^6409
        have hw : |(335110467/625000000 : ℝ)|=(335110467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266108921/1250000000 : ℝ)|^8457 ≤ (12985513974549/100000000000000 : ℝ)^6409
        have hw : |(-266108921/1250000000 : ℝ)|=(266108921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8253911/15625000 : ℝ)|^8457 ≤ (8615947025939/20000000000000 : ℝ)^6409
        have hw : |(8253911/15625000 : ℝ)|=(8253911/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361767507/10000000000 : ℝ)*x 0 + (105650061/200000000 : ℝ)*x 1 + (-2128871307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361767507/10000000000 : ℝ)^8457 ≤ (43934751261917/100000000000000 : ℝ)^6409 := by
    have hnat : (5361767507 : ℕ)^8457*100000000000000^6409 ≤ 43934751261917^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361767507 10000000000 43934751261917 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105650061/200000000 : ℝ)^8457 ≤ (43079735237307/100000000000000 : ℝ)^6409 := by
    have hnat : (105650061 : ℕ)^8457*100000000000000^6409 ≤ 43079735237307^6409*200000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105650061 200000000 43079735237307 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128871307/10000000000 : ℝ)^8457 ≤ (12985513483567/100000000000000 : ℝ)^6409 := by
    have hnat : (2128871307 : ℕ)^8457*100000000000000^6409 ≤ 12985513483567^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128871307 10000000000 12985513483567 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361767507/10000000000 : ℝ), (105650061/200000000 : ℝ), (-2128871307/10000000000 : ℝ)] ![(43934751261917/100000000000000 : ℝ), (43079735237307/100000000000000 : ℝ), (12985513483567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361767507/10000000000 : ℝ)|^8457 ≤ (43934751261917/100000000000000 : ℝ)^6409
        have hw : |(5361767507/10000000000 : ℝ)|=(5361767507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105650061/200000000 : ℝ)|^8457 ≤ (43079735237307/100000000000000 : ℝ)^6409
        have hw : |(105650061/200000000 : ℝ)|=(105650061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128871307/10000000000 : ℝ)|^8457 ≤ (12985513483567/100000000000000 : ℝ)^6409
        have hw : |(-2128871307/10000000000 : ℝ)|=(2128871307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2120520159/5000000000 : ℝ)*x 0 + (440313787/1000000000 : ℝ)*x 1 + (2201568967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120520159/5000000000 : ℝ)^8457 ≤ (16121334005057/50000000000000 : ℝ)^6409 := by
    have hnat : (2120520159 : ℕ)^8457*50000000000000^6409 ≤ 16121334005057^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120520159 5000000000 16121334005057 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440313787/1000000000 : ℝ)^8457 ≤ (33878665664587/100000000000000 : ℝ)^6409 := by
    have hnat : (440313787 : ℕ)^8457*100000000000000^6409 ≤ 33878665664587^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440313787 1000000000 33878665664587 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201568967/5000000000 : ℝ)^8457 ≤ (33878666314373/100000000000000 : ℝ)^6409 := by
    have hnat : (2201568967 : ℕ)^8457*100000000000000^6409 ≤ 33878666314373^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201568967 5000000000 33878666314373 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2120520159/5000000000 : ℝ), (440313787/1000000000 : ℝ), (2201568967/5000000000 : ℝ)] ![(16121334005057/50000000000000 : ℝ), (33878665664587/100000000000000 : ℝ), (33878666314373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2120520159/5000000000 : ℝ)|^8457 ≤ (16121334005057/50000000000000 : ℝ)^6409
        have hw : |(2120520159/5000000000 : ℝ)|=(2120520159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440313787/1000000000 : ℝ)|^8457 ≤ (33878665664587/100000000000000 : ℝ)^6409
        have hw : |(440313787/1000000000 : ℝ)|=(440313787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2201568967/5000000000 : ℝ)|^8457 ≤ (33878666314373/100000000000000 : ℝ)^6409
        have hw : |(2201568967/5000000000 : ℝ)|=(2201568967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_8 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-436481549/2000000000 : ℝ)*x 0 + (5219705899/10000000000 : ℝ)*x 1 + (1076824111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436481549/2000000000 : ℝ)^8457 ≤ (6709071894541/50000000000000 : ℝ)^6409 := by
    have hnat : (436481549 : ℕ)^8457*50000000000000^6409 ≤ 6709071894541^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436481549 2000000000 6709071894541 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219705899/10000000000 : ℝ)^8457 ≤ (2120262584641/5000000000000 : ℝ)^6409 := by
    have hnat : (5219705899 : ℕ)^8457*5000000000000^6409 ≤ 2120262584641^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219705899 10000000000 2120262584641 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076824111/2000000000 : ℝ)^8457 ≤ (5522075563233/12500000000000 : ℝ)^6409 := by
    have hnat : (1076824111 : ℕ)^8457*12500000000000^6409 ≤ 5522075563233^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076824111 2000000000 5522075563233 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-436481549/2000000000 : ℝ), (5219705899/10000000000 : ℝ), (1076824111/2000000000 : ℝ)] ![(6709071894541/50000000000000 : ℝ), (2120262584641/5000000000000 : ℝ), (5522075563233/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-436481549/2000000000 : ℝ)|^8457 ≤ (6709071894541/50000000000000 : ℝ)^6409
        have hw : |(-436481549/2000000000 : ℝ)|=(436481549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219705899/10000000000 : ℝ)|^8457 ≤ (2120262584641/5000000000000 : ℝ)^6409
        have hw : |(5219705899/10000000000 : ℝ)|=(5219705899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076824111/2000000000 : ℝ)|^8457 ≤ (5522075563233/12500000000000 : ℝ)^6409
        have hw : |(1076824111/2000000000 : ℝ)|=(1076824111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_9 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290165573/10000000000 : ℝ)*x 0 + (-83538119/400000000 : ℝ)*x 1 + (5384120683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290165573/10000000000 : ℝ)^8457 ≤ (5395276502877/12500000000000 : ℝ)^6409 := by
    have hnat : (5290165573 : ℕ)^8457*12500000000000^6409 ≤ 5395276502877^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290165573 10000000000 5395276502877 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83538119/400000000 : ℝ)^8457 ≤ (12661182073517/100000000000000 : ℝ)^6409 := by
    have hnat : (83538119 : ℕ)^8457*100000000000000^6409 ≤ 12661182073517^6409*400000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83538119 400000000 12661182073517 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384120683/10000000000 : ℝ)^8457 ≤ (22088302945853/50000000000000 : ℝ)^6409 := by
    have hnat : (5384120683 : ℕ)^8457*50000000000000^6409 ≤ 22088302945853^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384120683 10000000000 22088302945853 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290165573/10000000000 : ℝ), (-83538119/400000000 : ℝ), (5384120683/10000000000 : ℝ)] ![(5395276502877/12500000000000 : ℝ), (12661182073517/100000000000000 : ℝ), (22088302945853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290165573/10000000000 : ℝ)|^8457 ≤ (5395276502877/12500000000000 : ℝ)^6409
        have hw : |(5290165573/10000000000 : ℝ)|=(5290165573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83538119/400000000 : ℝ)|^8457 ≤ (12661182073517/100000000000000 : ℝ)^6409
        have hw : |(-83538119/400000000 : ℝ)|=(83538119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384120683/10000000000 : ℝ)|^8457 ≤ (22088302945853/50000000000000 : ℝ)^6409
        have hw : |(5384120683/10000000000 : ℝ)|=(5384120683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_10 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290165733/10000000000 : ℝ)*x 0 + (5384120537/10000000000 : ℝ)*x 1 + (-2088452957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290165733/10000000000 : ℝ)^8457 ≤ (26976383591/62500000000 : ℝ)^6409 := by
    have hnat : (5290165733 : ℕ)^8457*62500000000^6409 ≤ 26976383591^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290165733 10000000000 26976383591 62500000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5384120537/10000000000 : ℝ)^8457 ≤ (2208830215549/5000000000000 : ℝ)^6409 := by
    have hnat : (5384120537 : ℕ)^8457*5000000000000^6409 ≤ 2208830215549^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384120537 10000000000 2208830215549 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2088452957/10000000000 : ℝ)^8457 ≤ (6330590964761/50000000000000 : ℝ)^6409 := by
    have hnat : (2088452957 : ℕ)^8457*50000000000000^6409 ≤ 6330590964761^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088452957 10000000000 6330590964761 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290165733/10000000000 : ℝ), (5384120537/10000000000 : ℝ), (-2088452957/10000000000 : ℝ)] ![(26976383591/62500000000 : ℝ), (2208830215549/5000000000000 : ℝ), (6330590964761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290165733/10000000000 : ℝ)|^8457 ≤ (26976383591/62500000000 : ℝ)^6409
        have hw : |(5290165733/10000000000 : ℝ)|=(5290165733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5384120537/10000000000 : ℝ)|^8457 ≤ (2208830215549/5000000000000 : ℝ)^6409
        have hw : |(5384120537/10000000000 : ℝ)|=(5384120537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2088452957/10000000000 : ℝ)|^8457 ≤ (6330590964761/50000000000000 : ℝ)^6409
        have hw : |(-2088452957/10000000000 : ℝ)|=(2088452957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_11 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4476069399/10000000000 : ℝ)*x 0 + (4285502817/10000000000 : ℝ)*x 1 + (1071375683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4476069399/10000000000 : ℝ)^8457 ≤ (55393735063/160000000000 : ℝ)^6409 := by
    have hnat : (4476069399 : ℕ)^8457*160000000000^6409 ≤ 55393735063^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476069399 10000000000 55393735063 160000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4285502817/10000000000 : ℝ)^8457 ≤ (255386392281/781250000000 : ℝ)^6409 := by
    have hnat : (4285502817 : ℕ)^8457*781250000000^6409 ≤ 255386392281^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285502817 10000000000 255386392281 781250000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071375683/2500000000 : ℝ)^8457 ≤ (32689457356407/100000000000000 : ℝ)^6409 := by
    have hnat : (1071375683 : ℕ)^8457*100000000000000^6409 ≤ 32689457356407^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071375683 2500000000 32689457356407 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4476069399/10000000000 : ℝ), (4285502817/10000000000 : ℝ), (1071375683/2500000000 : ℝ)] ![(55393735063/160000000000 : ℝ), (255386392281/781250000000 : ℝ), (32689457356407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4476069399/10000000000 : ℝ)|^8457 ≤ (55393735063/160000000000 : ℝ)^6409
        have hw : |(4476069399/10000000000 : ℝ)|=(4476069399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4285502817/10000000000 : ℝ)|^8457 ≤ (255386392281/781250000000 : ℝ)^6409
        have hw : |(4285502817/10000000000 : ℝ)|=(4285502817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1071375683/2500000000 : ℝ)|^8457 ≤ (32689457356407/100000000000000 : ℝ)^6409
        have hw : |(1071375683/2500000000 : ℝ)|=(1071375683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_12 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038978741/10000000000 : ℝ)*x 0 + (5436110401/10000000000 : ℝ)*x 1 + (659302033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038978741/10000000000 : ℝ)^8457 ≤ (12266907455809/100000000000000 : ℝ)^6409 := by
    have hnat : (2038978741 : ℕ)^8457*100000000000000^6409 ≤ 12266907455809^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038978741 10000000000 12266907455809 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436110401/10000000000 : ℝ)^8457 ≤ (44740359245807/100000000000000 : ℝ)^6409 := by
    have hnat : (5436110401 : ℕ)^8457*100000000000000^6409 ≤ 44740359245807^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436110401 10000000000 44740359245807 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659302033/1250000000 : ℝ)^8457 ≤ (4299273328407/10000000000000 : ℝ)^6409 := by
    have hnat : (659302033 : ℕ)^8457*10000000000000^6409 ≤ 4299273328407^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659302033 1250000000 4299273328407 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038978741/10000000000 : ℝ), (5436110401/10000000000 : ℝ), (659302033/1250000000 : ℝ)] ![(12266907455809/100000000000000 : ℝ), (44740359245807/100000000000000 : ℝ), (4299273328407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038978741/10000000000 : ℝ)|^8457 ≤ (12266907455809/100000000000000 : ℝ)^6409
        have hw : |(-2038978741/10000000000 : ℝ)|=(2038978741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436110401/10000000000 : ℝ)|^8457 ≤ (44740359245807/100000000000000 : ℝ)^6409
        have hw : |(5436110401/10000000000 : ℝ)|=(5436110401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659302033/1250000000 : ℝ)|^8457 ≤ (4299273328407/10000000000000 : ℝ)^6409
        have hw : |(659302033/1250000000 : ℝ)|=(659302033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_13 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268373193/500000000 : ℝ)*x 0 + (-1066013493/5000000000 : ℝ)*x 1 + (2637207851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268373193/500000000 : ℝ)^8457 ≤ (43996353549877/100000000000000 : ℝ)^6409 := by
    have hnat : (268373193 : ℕ)^8457*100000000000000^6409 ≤ 43996353549877^6409*500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268373193 500000000 43996353549877 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066013493/5000000000 : ℝ)^8457 ≤ (13010919197803/100000000000000 : ℝ)^6409 := by
    have hnat : (1066013493 : ℕ)^8457*100000000000000^6409 ≤ 13010919197803^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066013493 5000000000 13010919197803 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637207851/5000000000 : ℝ)^8457 ≤ (8598545447851/20000000000000 : ℝ)^6409 := by
    have hnat : (2637207851 : ℕ)^8457*20000000000000^6409 ≤ 8598545447851^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637207851 5000000000 8598545447851 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268373193/500000000 : ℝ), (-1066013493/5000000000 : ℝ), (2637207851/5000000000 : ℝ)] ![(43996353549877/100000000000000 : ℝ), (13010919197803/100000000000000 : ℝ), (8598545447851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268373193/500000000 : ℝ)|^8457 ≤ (43996353549877/100000000000000 : ℝ)^6409
        have hw : |(268373193/500000000 : ℝ)|=(268373193/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066013493/5000000000 : ℝ)|^8457 ≤ (13010919197803/100000000000000 : ℝ)^6409
        have hw : |(-1066013493/5000000000 : ℝ)|=(1066013493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637207851/5000000000 : ℝ)|^8457 ≤ (8598545447851/20000000000000 : ℝ)^6409
        have hw : |(2637207851/5000000000 : ℝ)|=(2637207851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_14 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367463639/10000000000 : ℝ)*x 0 + (1318603971/2500000000 : ℝ)*x 1 + (-2132027039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367463639/10000000000 : ℝ)^8457 ≤ (43996351159503/100000000000000 : ℝ)^6409 := by
    have hnat : (5367463639 : ℕ)^8457*100000000000000^6409 ≤ 43996351159503^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367463639 10000000000 43996351159503 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318603971/2500000000 : ℝ)^8457 ≤ (42992729196829/100000000000000 : ℝ)^6409 := by
    have hnat : (1318603971 : ℕ)^8457*100000000000000^6409 ≤ 42992729196829^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318603971 2500000000 42992729196829 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132027039/10000000000 : ℝ)^8457 ≤ (3252729906149/25000000000000 : ℝ)^6409 := by
    have hnat : (2132027039 : ℕ)^8457*25000000000000^6409 ≤ 3252729906149^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132027039 10000000000 3252729906149 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367463639/10000000000 : ℝ), (1318603971/2500000000 : ℝ), (-2132027039/10000000000 : ℝ)] ![(43996351159503/100000000000000 : ℝ), (42992729196829/100000000000000 : ℝ), (3252729906149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367463639/10000000000 : ℝ)|^8457 ≤ (43996351159503/100000000000000 : ℝ)^6409
        have hw : |(5367463639/10000000000 : ℝ)|=(5367463639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318603971/2500000000 : ℝ)|^8457 ≤ (42992729196829/100000000000000 : ℝ)^6409
        have hw : |(1318603971/2500000000 : ℝ)|=(1318603971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132027039/10000000000 : ℝ)|^8457 ≤ (3252729906149/25000000000000 : ℝ)^6409
        have hw : |(-2132027039/10000000000 : ℝ)|=(2132027039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_box_15 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (131940063/312500000 : ℝ)*x 0 + (4412494073/10000000000 : ℝ)*x 1 + (1103123603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131940063/312500000 : ℝ)^8457 ≤ (16026307783843/50000000000000 : ℝ)^6409 := by
    have hnat : (131940063 : ℕ)^8457*50000000000000^6409 ≤ 16026307783843^6409*312500000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131940063 312500000 16026307783843 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412494073/10000000000 : ℝ)^8457 ≤ (8493422621239/25000000000000 : ℝ)^6409 := by
    have hnat : (4412494073 : ℕ)^8457*25000000000000^6409 ≤ 8493422621239^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412494073 10000000000 8493422621239 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103123603/2500000000 : ℝ)^8457 ≤ (271789551433/800000000000 : ℝ)^6409 := by
    have hnat : (1103123603 : ℕ)^8457*800000000000^6409 ≤ 271789551433^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103123603 2500000000 271789551433 800000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131940063/312500000 : ℝ), (4412494073/10000000000 : ℝ), (1103123603/2500000000 : ℝ)] ![(16026307783843/50000000000000 : ℝ), (8493422621239/25000000000000 : ℝ), (271789551433/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131940063/312500000 : ℝ)|^8457 ≤ (16026307783843/50000000000000 : ℝ)^6409
        have hw : |(131940063/312500000 : ℝ)|=(131940063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412494073/10000000000 : ℝ)|^8457 ≤ (8493422621239/25000000000000 : ℝ)^6409
        have hw : |(4412494073/10000000000 : ℝ)|=(4412494073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103123603/2500000000 : ℝ)|^8457 ≤ (271789551433/800000000000 : ℝ)^6409
        have hw : |(1103123603/2500000000 : ℝ)|=(1103123603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62251/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11879/20000 : ℝ) ∧ (40087/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41697/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2301/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2301/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2301/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2301/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2301/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2301/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2301/20000 : ℝ) ^ (1057/256 : ℝ) ≤ (265166651198753/2000000000000000000 : ℝ) := by
    have hpowers : (2301/20000 : ℝ)^1057 ≤ (265166651198753/2000000000000000000 : ℝ)^256 := by
      have hnat : (2301 : ℕ)^1057*2000000000000000000^256 ≤ 265166651198753^256*20000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2301 20000 265166651198753 2000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2301/20000 : ℝ)) (X := (265166651198753/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2823/20000 : ℝ) ^ (1057/256 : ℝ) ≤ (3083983751213907/10000000000000000000 : ℝ) := by
    have hpowers : (2823/20000 : ℝ)^1057 ≤ (3083983751213907/10000000000000000000 : ℝ)^256 := by
      have hnat : (2823 : ℕ)^1057*10000000000000000000^256 ≤ 3083983751213907^256*20000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 20000 3083983751213907 10000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/20000 : ℝ)) (X := (3083983751213907/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000265166651198753/1000000000000000000 : ℝ) ≤ (2000128431113411/2000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (1000265166651198753/1000000000000000000 : ℝ)^256 ≤ (2000128431113411/2000000000000000 : ℝ)^1057 := by
      have hnat : (1000265166651198753 : ℕ)^256*2000000000000000^1057 ≤ 2000128431113411^1057*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000265166651198753 1000000000000000000 2000128431113411 2000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000128431113411/2000000000000000 : ℝ)) (X := (1000265166651198753/1000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250551227125900959/1250000000000000000 : ℝ) ≤ (1250133482092419/1250000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (1250551227125900959/1250000000000000000 : ℝ)^256 ≤ (1250133482092419/1250000000000000 : ℝ)^1057 := by
      have hnat : (1250551227125900959 : ℕ)^256*1250000000000000^1057 ≤ 1250133482092419^1057*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250551227125900959 1250000000000000000 1250133482092419 1250000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250133482092419/1250000000000000 : ℝ)) (X := (1250551227125900959/1250000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003083983751213907/5000000000000000000 : ℝ) ≤ (10001493557911649/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (5003083983751213907/5000000000000000000 : ℝ)^256 ≤ (10001493557911649/10000000000000000 : ℝ)^1057 := by
      have hnat : (5003083983751213907 : ℕ)^256*10000000000000000^1057 ≤ 10001493557911649^1057*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003083983751213907 5000000000000000000 10001493557911649 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001493557911649/10000000000000000 : ℝ)) (X := (5003083983751213907/5000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(265166651198753/2000000000000000000 : ℝ) ≤ ((434864677367590993/435000000000000000 : ℝ)+2*(425701172297/261000000000000 : ℝ)*(2301/20000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (434864677367590993/435000000000000000 : ℝ)+2*(425701172297/261000000000000 : ℝ)*(2301/20000 : ℝ)=(2000128431113411/2000000000000000 : ℝ) by norm_num, show 1+2*(265166651198753/2000000000000000000 : ℝ)=(1000265166651198753/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3083983751213907/10000000000000000000 : ℝ)+(265166651198753/2000000000000000000 : ℝ) ≤ ((434864677367590993/435000000000000000 : ℝ)+(425701172297/261000000000000 : ℝ)*((2823/20000 : ℝ)+(2301/20000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (434864677367590993/435000000000000000 : ℝ)+(425701172297/261000000000000 : ℝ)*((2823/20000 : ℝ)+(2301/20000 : ℝ))=(1250133482092419/1250000000000000 : ℝ) by norm_num, show 1+(3083983751213907/10000000000000000000 : ℝ)+(265166651198753/2000000000000000000 : ℝ)=(1250551227125900959/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3083983751213907/10000000000000000000 : ℝ) ≤ ((434864677367590993/435000000000000000 : ℝ)+2*(425701172297/261000000000000 : ℝ)*(2823/20000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (434864677367590993/435000000000000000 : ℝ)+2*(425701172297/261000000000000 : ℝ)*(2823/20000 : ℝ)=(10001493557911649/10000000000000000 : ℝ) by norm_num, show 1+2*(3083983751213907/10000000000000000000 : ℝ)=(5003083983751213907/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (434864677367590993/435000000000000000 : ℝ)*(X 1 0+X 2 0)+(425701172297/261000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (434864677367590993/435000000000000000 : ℝ)) (alpha := (425701172297/261000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (434864677367590993/435000000000000000 : ℝ)*(X 0 1+X 2 1)+(425701172297/261000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (434864677367590993/435000000000000000 : ℝ)) (alpha := (425701172297/261000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (434864677367590993/435000000000000000 : ℝ)*(X 0 2+X 1 2)+(425701172297/261000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (2301/20000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (434864677367590993/435000000000000000 : ℝ)) (alpha := (425701172297/261000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-397372961/2000000000 : ℝ)*X 0 0+(107490153/200000000 : ℝ)*X 0 1+(5374507319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296941867/10000000000 : ℝ)*X 1 0+(-130771059/625000000 : ℝ)*X 1 1+(5374507653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296941823/10000000000 : ℝ)*X 2 0+(1074901493/2000000000 : ℝ)*X 2 1+(-2092337257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4454081819/10000000000 : ℝ)*X 0 0+(107415929/250000000 : ℝ)*X 0 1+(4296637037/10000000000 : ℝ)*X 0 2+(4454081819/10000000000 : ℝ)*X 1 0+(107415929/250000000 : ℝ)*X 1 1+(4296637037/10000000000 : ℝ)*X 1 2+(4454081819/10000000000 : ℝ)*X 2 0+(107415929/250000000 : ℝ)*X 2 1+(4296637037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1117137141/5000000000 : ℝ)*X 0 0+(5282503099/10000000000 : ℝ)*X 0 1+(5282503197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((335110467/625000000 : ℝ)*X 1 0+(-266108921/1250000000 : ℝ)*X 1 1+(8253911/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5361767507/10000000000 : ℝ)*X 2 0+(105650061/200000000 : ℝ)*X 2 1+(-2128871307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2120520159/5000000000 : ℝ)*X 0 0+(440313787/1000000000 : ℝ)*X 0 1+(2201568967/5000000000 : ℝ)*X 0 2+(2120520159/5000000000 : ℝ)*X 1 0+(440313787/1000000000 : ℝ)*X 1 1+(2201568967/5000000000 : ℝ)*X 1 2+(2120520159/5000000000 : ℝ)*X 2 0+(440313787/1000000000 : ℝ)*X 2 1+(2201568967/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-436481549/2000000000 : ℝ)*X 0 0+(5219705899/10000000000 : ℝ)*X 0 1+(1076824111/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290165573/10000000000 : ℝ)*X 1 0+(-83538119/400000000 : ℝ)*X 1 1+(5384120683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290165733/10000000000 : ℝ)*X 2 0+(5384120537/10000000000 : ℝ)*X 2 1+(-2088452957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4476069399/10000000000 : ℝ)*X 0 0+(4285502817/10000000000 : ℝ)*X 0 1+(1071375683/2500000000 : ℝ)*X 0 2+(4476069399/10000000000 : ℝ)*X 1 0+(4285502817/10000000000 : ℝ)*X 1 1+(1071375683/2500000000 : ℝ)*X 1 2+(4476069399/10000000000 : ℝ)*X 2 0+(4285502817/10000000000 : ℝ)*X 2 1+(1071375683/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2038978741/10000000000 : ℝ)*X 0 0+(5436110401/10000000000 : ℝ)*X 0 1+(659302033/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((268373193/500000000 : ℝ)*X 1 0+(-1066013493/5000000000 : ℝ)*X 1 1+(2637207851/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5367463639/10000000000 : ℝ)*X 2 0+(1318603971/2500000000 : ℝ)*X 2 1+(-2132027039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((131940063/312500000 : ℝ)*X 0 0+(4412494073/10000000000 : ℝ)*X 0 1+(1103123603/2500000000 : ℝ)*X 0 2+(131940063/312500000 : ℝ)*X 1 0+(4412494073/10000000000 : ℝ)*X 1 1+(1103123603/2500000000 : ℝ)*X 1 2+(131940063/312500000 : ℝ)*X 2 0+(4412494073/10000000000 : ℝ)*X 2 1+(1103123603/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62251/100000 : ℝ) ≤ (-84619173114078464848481091091/135937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (929159/12500000000000 : ℝ)*(lower0) + (52750051/100000000000000 : ℝ)*(lower2) + (15760291/25000000000000 : ℝ)*(lower3) + (41232351/100000000000000 : ℝ)*(lower4) + (719179/50000000000000 : ℝ)*(lower5) + (100529369610533/2500000000000 : ℝ)*(major0) + (100529369610533/2500000000000 : ℝ)*(major1) + (100529369610533/2500000000000 : ℝ)*(major2) + (5971597/250000000000 : ℝ)*(sp1) + (707120859/20000000000000 : ℝ)*(sp2) + (84611607052277/1562500000000 : ℝ)*(sp4) + (338446278919183/6250000000000 : ℝ)*(sp5) + (5415139315741433/100000000000000 : ℝ)*(sp6) + (66198906163409/2500000000000 : ℝ)*(sp7) + (66198906163409/2500000000000 : ℝ)*(f.failure) + (84611607052277/1562500000000 : ℝ)*(f.sum) + (569294424479/326250000000000000000000000 : ℝ)*base66 + (26444135380292807/3262500000000000000000000000000 : ℝ)*base67 + (36044993027492807/3262500000000000000000000000000 : ℝ)*base69 + (25976998154492807/3262500000000000000000000000000 : ℝ)*base71 + (8298056867519/326250000000000000000000000 : ℝ)*base74 + (33664982625692807/3262500000000000000000000000000 : ℝ)*base75 + (63962736858242807/3262500000000000000000000000000 : ℝ)*base77 + (186000148088869693/3262500000000000000000000000000 : ℝ)*base80 + (350240508733/652500000000000000000000000 : ℝ)*base82 + (2669733/250000000000000000000 : ℝ)*base90 + (2669733/250000000000000000000 : ℝ)*base92 + (2669733/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11879/20000 : ℝ) ≤ (3445064135750421928496753793/5800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (98638083/100000000000000 : ℝ)*(upper2) + (142797963/100000000000000 : ℝ)*(upper3) + (9405413/50000000000000 : ℝ)*(lower5) + (3269867946201/80000000000 : ℝ)*(major0) + (3269867946201/80000000000 : ℝ)*(major1) + (3269867946201/80000000000 : ℝ)*(major2) + (5463346755313589/100000000000000 : ℝ)*(sp0) + (1092668704727387/20000000000000 : ℝ)*(sp1) + (2731638960728859/50000000000000 : ℝ)*(sp2) + (1345731501261653/50000000000000 : ℝ)*(sp3) + (4210336897/100000000000000 : ℝ)*(sp5) + (489330121/50000000000000 : ℝ)*(sp8) + (69812516113/100000000000000 : ℝ)*(sp10) + (59909834377/100000000000000 : ℝ)*(sp11) + (2691522912357683/100000000000000 : ℝ)*(f.failure) + (5463347733973831/100000000000000 : ℝ)*(f.sum) + (249604898633/29000000000000000000000000 : ℝ)*base66 + (56865724885669/11600000000000000000000000000 : ℝ)*base68 + (17186121838331/11600000000000000000000000000 : ℝ)*base69 + (143681988878069/11600000000000000000000000000 : ℝ)*base72 + (16462059517/7250000000000000000000000 : ℝ)*base73 + (96998457676069/11600000000000000000000000000 : ℝ)*base76 + (91461383960469/11600000000000000000000000000 : ℝ)*base78 + (33545207055531/11600000000000000000000000000 : ℝ)*base79 + (41220911937/14500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (40072529/10000000000000000000000 : ℝ)*base89 + (40072529/10000000000000000000000 : ℝ)*base91 + (40072529/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40087/50000 : ℝ) ≤ (100220064711701219379469125237/125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61955947/100000000000000 : ℝ)*(upper0) + (28320683/50000000000000 : ℝ)*(upper1) + (62665843/100000000000000 : ℝ)*(upper4) + (4553801784848339/100000000000000 : ℝ)*(major0) + (4553801784848339/100000000000000 : ℝ)*(major1) + (4553801784848339/100000000000000 : ℝ)*(major2) + (72516957839/50000000000000 : ℝ)*(sp1) + (46951945501/50000000000000 : ℝ)*(sp2) + (5138826999/20000000000000 : ℝ)*(sp3) + (15155501/3125000000000 : ℝ)*(sp4) + (380136558257409/6250000000000 : ℝ)*(sp8) + (3041020191589449/50000000000000 : ℝ)*(sp9) + (3041045756601787/50000000000000 : ℝ)*(sp10) + (749666776969327/25000000000000 : ℝ)*(sp11) + (187418300125769/6250000000000 : ℝ)*(f.failure) + (380136588568411/6250000000000 : ℝ)*(f.sum) + (13367662723/450000000000000000000000000 : ℝ)*base66 + (12611052926056789/4500000000000000000000000000000 : ℝ)*base67 + (15545248968556789/4500000000000000000000000000000 : ℝ)*base69 + (326421399556789/4500000000000000000000000000000 : ℝ)*base71 + (7468539444827/450000000000000000000000000 : ℝ)*base73 + (42440917170556789/4500000000000000000000000000000 : ℝ)*base75 + (3766495136443211/4500000000000000000000000000000 : ℝ)*base78 + (230565335678056789/4500000000000000000000000000000 : ℝ)*base79 + (2256448561577/450000000000000000000000000 : ℝ)*base81 + (6628947/625000000000000000000 : ℝ)*base89 + (6628947/625000000000000000000 : ℝ)*base91 + (6628947/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41697/50000 : ℝ) ≤ (-625433820882793712977532657633/750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (718511/1000000000000 : ℝ)*(upper3) + (66807849/50000000000000 : ℝ)*(lower4) + (139834329/100000000000000 : ℝ)*(upper5) + (4589464412082017/100000000000000 : ℝ)*(major0) + (4589464412082017/100000000000000 : ℝ)*(major1) + (4589464412082017/100000000000000 : ℝ)*(major2) + (30500231663/100000000000000 : ℝ)*(sp4) + (68639411257/12500000000000 : ℝ)*(sp5) + (543762918563/100000000000000 : ℝ)*(sp6) + (278080643507/100000000000000 : ℝ)*(sp7) + (6184518628394597/100000000000000 : ℝ)*(sp12) + (1546000003334051/25000000000000 : ℝ)*(sp13) + (386500335356731/6250000000000 : ℝ)*(sp14) + (18886866710001/625000000000 : ℝ)*(sp15) + (755544188560917/25000000000000 : ℝ)*(f.failure) + (309227456431313/5000000000000 : ℝ)*(f.sum) + (115673545301899/13050000000000000000000000000 : ℝ)*base65 + (745251031027336357/130500000000000000000000000000000 : ℝ)*base68 + (391082433546163643/130500000000000000000000000000000 : ℝ)*base69 + (605041159474336357/130500000000000000000000000000000 : ℝ)*base72 + (76478397848149/13050000000000000000000000000 : ℝ)*base73 + (1099200582838336357/130500000000000000000000000000000 : ℝ)*base76 + (1291151736320836357/130500000000000000000000000000000 : ℝ)*base78 + (46462012882663643/130500000000000000000000000000000 : ℝ)*base79 + (11578236310399/13050000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (29499271/2500000000000000000000 : ℝ)*base89 + (29499271/2500000000000000000000 : ℝ)*base91 + (29499271/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1264_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11879/20000 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41697/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1264_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1264_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11879/20000 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41697/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1264_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2301/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11879/20000 : ℝ) else (40087/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41697/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
