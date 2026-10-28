-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:59:31.905772+00:00
-- url     : https://prove2.me/submissions/55608408-af26-4050-824a-192f8a9af9e9

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
theorem support_rectangle_w1192_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876086281/10000000000 : ℝ)*x 0 + (3021422863/5000000000 : ℝ)*x 1 + (4786763313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876086281/10000000000 : ℝ)^8385 ≤ (1365500006637/12500000000000 : ℝ)^6337 := by
    have hnat : (1876086281 : ℕ)^8385*12500000000000^6337 ≤ 1365500006637^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876086281 10000000000 1365500006637 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021422863/5000000000 : ℝ)^8385 ≤ (6418785488937/12500000000000 : ℝ)^6337 := by
    have hnat : (3021422863 : ℕ)^8385*12500000000000^6337 ≤ 6418785488937^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021422863 5000000000 6418785488937 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4786763313/10000000000 : ℝ)^8385 ≤ (75451432057/200000000000 : ℝ)^6337 := by
    have hnat : (4786763313 : ℕ)^8385*200000000000^6337 ≤ 75451432057^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786763313 10000000000 75451432057 200000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876086281/10000000000 : ℝ), (3021422863/5000000000 : ℝ), (4786763313/10000000000 : ℝ)] ![(1365500006637/12500000000000 : ℝ), (6418785488937/12500000000000 : ℝ), (75451432057/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876086281/10000000000 : ℝ)|^8385 ≤ (1365500006637/12500000000000 : ℝ)^6337
        have hw : |(-1876086281/10000000000 : ℝ)|=(1876086281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021422863/5000000000 : ℝ)|^8385 ≤ (6418785488937/12500000000000 : ℝ)^6337
        have hw : |(3021422863/5000000000 : ℝ)|=(3021422863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4786763313/10000000000 : ℝ)|^8385 ≤ (75451432057/200000000000 : ℝ)^6337
        have hw : |(4786763313/10000000000 : ℝ)|=(4786763313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1102795279/2000000000 : ℝ)*x 0 + (-2595533773/10000000000 : ℝ)*x 1 + (4786763281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102795279/2000000000 : ℝ)^8385 ≤ (9097900550157/20000000000000 : ℝ)^6337 := by
    have hnat : (1102795279 : ℕ)^8385*20000000000000^6337 ≤ 9097900550157^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102795279 2000000000 9097900550157 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2595533773/10000000000 : ℝ)^8385 ≤ (16784781542167/100000000000000 : ℝ)^6337 := by
    have hnat : (2595533773 : ℕ)^8385*100000000000000^6337 ≤ 16784781542167^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595533773 10000000000 16784781542167 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4786763281/10000000000 : ℝ)^8385 ≤ (37725715694793/100000000000000 : ℝ)^6337 := by
    have hnat : (4786763281 : ℕ)^8385*100000000000000^6337 ≤ 37725715694793^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4786763281 10000000000 37725715694793 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102795279/2000000000 : ℝ), (-2595533773/10000000000 : ℝ), (4786763281/10000000000 : ℝ)] ![(9097900550157/20000000000000 : ℝ), (16784781542167/100000000000000 : ℝ), (37725715694793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102795279/2000000000 : ℝ)|^8385 ≤ (9097900550157/20000000000000 : ℝ)^6337
        have hw : |(1102795279/2000000000 : ℝ)|=(1102795279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2595533773/10000000000 : ℝ)|^8385 ≤ (16784781542167/100000000000000 : ℝ)^6337
        have hw : |(-2595533773/10000000000 : ℝ)|=(2595533773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4786763281/10000000000 : ℝ)|^8385 ≤ (37725715694793/100000000000000 : ℝ)^6337
        have hw : |(4786763281/10000000000 : ℝ)|=(4786763281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513976697/10000000000 : ℝ)*x 0 + (598345373/1250000000 : ℝ)*x 1 + (-648883437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513976697/10000000000 : ℝ)^8385 ≤ (45489506047433/100000000000000 : ℝ)^6337 := by
    have hnat : (5513976697 : ℕ)^8385*100000000000000^6337 ≤ 45489506047433^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513976697 10000000000 45489506047433 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598345373/1250000000 : ℝ)^8385 ≤ (18862856298789/50000000000000 : ℝ)^6337 := by
    have hnat : (598345373 : ℕ)^8385*50000000000000^6337 ≤ 18862856298789^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598345373 1250000000 18862856298789 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648883437/2500000000 : ℝ)^8385 ≤ (2098097666031/12500000000000 : ℝ)^6337 := by
    have hnat : (648883437 : ℕ)^8385*12500000000000^6337 ≤ 2098097666031^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648883437 2500000000 2098097666031 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513976697/10000000000 : ℝ), (598345373/1250000000 : ℝ), (-648883437/2500000000 : ℝ)] ![(45489506047433/100000000000000 : ℝ), (18862856298789/50000000000000 : ℝ), (2098097666031/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513976697/10000000000 : ℝ)|^8385 ≤ (45489506047433/100000000000000 : ℝ)^6337
        have hw : |(5513976697/10000000000 : ℝ)|=(5513976697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598345373/1250000000 : ℝ)|^8385 ≤ (18862856298789/50000000000000 : ℝ)^6337
        have hw : |(598345373/1250000000 : ℝ)|=(598345373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-648883437/2500000000 : ℝ)|^8385 ≤ (2098097666031/12500000000000 : ℝ)^6337
        have hw : |(-648883437/2500000000 : ℝ)|=(648883437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4196977027/10000000000 : ℝ)*x 0 + (3118874749/10000000000 : ℝ)*x 1 + (5642349547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196977027/10000000000 : ℝ)^8385 ≤ (31701276024561/100000000000000 : ℝ)^6337 := by
    have hnat : (4196977027 : ℕ)^8385*100000000000000^6337 ≤ 31701276024561^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196977027 10000000000 31701276024561 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118874749/10000000000 : ℝ)^8385 ≤ (21402648582589/100000000000000 : ℝ)^6337 := by
    have hnat : (3118874749 : ℕ)^8385*100000000000000^6337 ≤ 21402648582589^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118874749 10000000000 21402648582589 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5642349547/10000000000 : ℝ)^8385 ≤ (2931004710827/6250000000000 : ℝ)^6337 := by
    have hnat : (5642349547 : ℕ)^8385*6250000000000^6337 ≤ 2931004710827^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5642349547 10000000000 2931004710827 6250000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196977027/10000000000 : ℝ), (3118874749/10000000000 : ℝ), (5642349547/10000000000 : ℝ)] ![(31701276024561/100000000000000 : ℝ), (21402648582589/100000000000000 : ℝ), (2931004710827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196977027/10000000000 : ℝ)|^8385 ≤ (31701276024561/100000000000000 : ℝ)^6337
        have hw : |(4196977027/10000000000 : ℝ)|=(4196977027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118874749/10000000000 : ℝ)|^8385 ≤ (21402648582589/100000000000000 : ℝ)^6337
        have hw : |(3118874749/10000000000 : ℝ)|=(3118874749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5642349547/10000000000 : ℝ)|^8385 ≤ (2931004710827/6250000000000 : ℝ)^6337
        have hw : |(5642349547/10000000000 : ℝ)|=(5642349547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-940543169/5000000000 : ℝ)*x 0 + (481913961/1000000000 : ℝ)*x 1 + (6009327631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (940543169/5000000000 : ℝ)^8385 ≤ (10962539908719/100000000000000 : ℝ)^6337 := by
    have hnat : (940543169 : ℕ)^8385*100000000000000^6337 ≤ 10962539908719^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940543169 5000000000 10962539908719 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481913961/1000000000 : ℝ)^8385 ≤ (38063715293187/100000000000000 : ℝ)^6337 := by
    have hnat : (481913961 : ℕ)^8385*100000000000000^6337 ≤ 38063715293187^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481913961 1000000000 38063715293187 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6009327631/10000000000 : ℝ)^8385 ≤ (25486872393857/50000000000000 : ℝ)^6337 := by
    have hnat : (6009327631 : ℕ)^8385*50000000000000^6337 ≤ 25486872393857^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009327631 10000000000 25486872393857 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-940543169/5000000000 : ℝ), (481913961/1000000000 : ℝ), (6009327631/10000000000 : ℝ)] ![(10962539908719/100000000000000 : ℝ), (38063715293187/100000000000000 : ℝ), (25486872393857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-940543169/5000000000 : ℝ)|^8385 ≤ (10962539908719/100000000000000 : ℝ)^6337
        have hw : |(-940543169/5000000000 : ℝ)|=(940543169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481913961/1000000000 : ℝ)|^8385 ≤ (38063715293187/100000000000000 : ℝ)^6337
        have hw : |(481913961/1000000000 : ℝ)|=(481913961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6009327631/10000000000 : ℝ)|^8385 ≤ (25486872393857/50000000000000 : ℝ)^6337
        have hw : |(6009327631/10000000000 : ℝ)|=(6009327631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172435623/10000000000 : ℝ)*x 0 + (-343242371/2500000000 : ℝ)*x 1 + (6009327237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172435623/10000000000 : ℝ)^8385 ≤ (41799077568389/100000000000000 : ℝ)^6337 := by
    have hnat : (5172435623 : ℕ)^8385*100000000000000^6337 ≤ 41799077568389^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172435623 10000000000 41799077568389 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343242371/2500000000 : ℝ)^8385 ≤ (722718204667/10000000000000 : ℝ)^6337 := by
    have hnat : (343242371 : ℕ)^8385*10000000000000^6337 ≤ 722718204667^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343242371 2500000000 722718204667 10000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6009327237/10000000000 : ℝ)^8385 ≤ (1592929386423/3125000000000 : ℝ)^6337 := by
    have hnat : (6009327237 : ℕ)^8385*3125000000000^6337 ≤ 1592929386423^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009327237 10000000000 1592929386423 3125000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172435623/10000000000 : ℝ), (-343242371/2500000000 : ℝ), (6009327237/10000000000 : ℝ)] ![(41799077568389/100000000000000 : ℝ), (722718204667/10000000000000 : ℝ), (1592929386423/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172435623/10000000000 : ℝ)|^8385 ≤ (41799077568389/100000000000000 : ℝ)^6337
        have hw : |(5172435623/10000000000 : ℝ)|=(5172435623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343242371/2500000000 : ℝ)|^8385 ≤ (722718204667/10000000000000 : ℝ)^6337
        have hw : |(-343242371/2500000000 : ℝ)|=(343242371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6009327237/10000000000 : ℝ)|^8385 ≤ (1592929386423/3125000000000 : ℝ)^6337
        have hw : |(6009327237/10000000000 : ℝ)|=(6009327237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172435541/10000000000 : ℝ)*x 0 + (600932747/1000000000 : ℝ)*x 1 + (-274593847/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172435541/10000000000 : ℝ)^8385 ≤ (2089953834579/5000000000000 : ℝ)^6337 := by
    have hnat : (5172435541 : ℕ)^8385*5000000000000^6337 ≤ 2089953834579^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172435541 10000000000 2089953834579 5000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600932747/1000000000 : ℝ)^8385 ≤ (25486871490341/50000000000000 : ℝ)^6337 := by
    have hnat : (600932747 : ℕ)^8385*50000000000000^6337 ≤ 25486871490341^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600932747 1000000000 25486871490341 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274593847/2000000000 : ℝ)^8385 ≤ (180679507809/2500000000000 : ℝ)^6337 := by
    have hnat : (274593847 : ℕ)^8385*2500000000000^6337 ≤ 180679507809^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274593847 2000000000 180679507809 2500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172435541/10000000000 : ℝ), (600932747/1000000000 : ℝ), (-274593847/2000000000 : ℝ)] ![(2089953834579/5000000000000 : ℝ), (25486871490341/50000000000000 : ℝ), (180679507809/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172435541/10000000000 : ℝ)|^8385 ≤ (2089953834579/5000000000000 : ℝ)^6337
        have hw : |(5172435541/10000000000 : ℝ)|=(5172435541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600932747/1000000000 : ℝ)|^8385 ≤ (25486871490341/50000000000000 : ℝ)^6337
        have hw : |(600932747/1000000000 : ℝ)|=(600932747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274593847/2000000000 : ℝ)|^8385 ≤ (180679507809/2500000000000 : ℝ)^6337
        have hw : |(-274593847/2000000000 : ℝ)|=(274593847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103511101/5000000000 : ℝ)*x 0 + (2788652421/5000000000 : ℝ)*x 1 + (31862133/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103511101/5000000000 : ℝ)^8385 ≤ (31801710973127/100000000000000 : ℝ)^6337 := by
    have hnat : (2103511101 : ℕ)^8385*100000000000000^6337 ≤ 31801710973127^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103511101 5000000000 31801710973127 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2788652421/5000000000 : ℝ)^8385 ≤ (11545519777159/25000000000000 : ℝ)^6337 := by
    have hnat : (2788652421 : ℕ)^8385*25000000000000^6337 ≤ 11545519777159^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788652421 5000000000 11545519777159 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31862133/100000000 : ℝ)^8385 ≤ (22016209904869/100000000000000 : ℝ)^6337 := by
    have hnat : (31862133 : ℕ)^8385*100000000000000^6337 ≤ 22016209904869^6337*100000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31862133 100000000 22016209904869 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103511101/5000000000 : ℝ), (2788652421/5000000000 : ℝ), (31862133/100000000 : ℝ)] ![(31801710973127/100000000000000 : ℝ), (11545519777159/25000000000000 : ℝ), (22016209904869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103511101/5000000000 : ℝ)|^8385 ≤ (31801710973127/100000000000000 : ℝ)^6337
        have hw : |(2103511101/5000000000 : ℝ)|=(2103511101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2788652421/5000000000 : ℝ)|^8385 ≤ (11545519777159/25000000000000 : ℝ)^6337
        have hw : |(2788652421/5000000000 : ℝ)|=(2788652421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31862133/100000000 : ℝ)|^8385 ≤ (22016209904869/100000000000000 : ℝ)^6337
        have hw : |(31862133/100000000 : ℝ)|=(31862133/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (309/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (221/800 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (131/32 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^131 ≤ (0 : ℝ)^32 := by
      have hnat : (0 : ℕ)^131*1^32 ≤ 0^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (131/32 : ℝ) ≤ (1174635423782711621/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^131 ≤ (1174635423782711621/50000000000000000000 : ℝ)^32 := by
      have hnat : (2 : ℕ)^131*50000000000000000000^32 ≤ 1174635423782711621^32*5^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1174635423782711621 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1174635423782711621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (1 : ℝ)^32 ≤ (1 : ℝ)^131 := by
      have hnat : (1 : ℕ)^32*1^131 ≤ 1^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (51174635423782711621/50000000000000000000 : ℝ) ≤ (2514221059540817/2500000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (51174635423782711621/50000000000000000000 : ℝ)^32 ≤ (2514221059540817/2500000000000000 : ℝ)^131 := by
      have hnat : (51174635423782711621 : ℕ)^32*2500000000000000^131 ≤ 2514221059540817^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51174635423782711621 50000000000000000000 2514221059540817 2500000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2514221059540817/2500000000000000 : ℝ)) (X := (51174635423782711621/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (26174635423782711621/25000000000000000000 : ℝ) ≤ (1264221059540817/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (26174635423782711621/25000000000000000000 : ℝ)^32 ≤ (1264221059540817/1250000000000000 : ℝ)^131 := by
      have hnat : (26174635423782711621 : ℕ)^32*1250000000000000^131 ≤ 1264221059540817^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26174635423782711621 25000000000000000000 1264221059540817 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1264221059540817/1250000000000000 : ℝ)) (X := (26174635423782711621/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(14221059540817/1000000000000000 : ℝ)*(0 : ℝ))^(131/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(14221059540817/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1174635423782711621/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(14221059540817/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(131/32 : ℝ) := by
    rw [show (1 : ℝ)+(14221059540817/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2514221059540817/2500000000000000 : ℝ) by norm_num, show 1+(1174635423782711621/50000000000000000000 : ℝ)+(0 : ℝ)=(51174635423782711621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1174635423782711621/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(14221059540817/1000000000000000 : ℝ)*(2/5 : ℝ))^(131/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(14221059540817/1000000000000000 : ℝ)*(2/5 : ℝ)=(1264221059540817/1250000000000000 : ℝ) by norm_num, show 1+2*(1174635423782711621/50000000000000000000 : ℝ)=(26174635423782711621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(14221059540817/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14221059540817/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(14221059540817/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14221059540817/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(14221059540817/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (14221059540817/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1876086281/10000000000 : ℝ)*X 0 0+(3021422863/5000000000 : ℝ)*X 0 1+(4786763313/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1102795279/2000000000 : ℝ)*X 1 0+(-2595533773/10000000000 : ℝ)*X 1 1+(4786763281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5513976697/10000000000 : ℝ)*X 2 0+(598345373/1250000000 : ℝ)*X 2 1+(-648883437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196977027/10000000000 : ℝ)*X 0 0+(3118874749/10000000000 : ℝ)*X 0 1+(5642349547/10000000000 : ℝ)*X 0 2+(4196977027/10000000000 : ℝ)*X 1 0+(3118874749/10000000000 : ℝ)*X 1 1+(5642349547/10000000000 : ℝ)*X 1 2+(4196977027/10000000000 : ℝ)*X 2 0+(3118874749/10000000000 : ℝ)*X 2 1+(5642349547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-940543169/5000000000 : ℝ)*X 0 0+(481913961/1000000000 : ℝ)*X 0 1+(6009327631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172435623/10000000000 : ℝ)*X 1 0+(-343242371/2500000000 : ℝ)*X 1 1+(6009327237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5172435541/10000000000 : ℝ)*X 2 0+(600932747/1000000000 : ℝ)*X 2 1+(-274593847/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103511101/5000000000 : ℝ)*X 0 0+(2788652421/5000000000 : ℝ)*X 0 1+(31862133/100000000 : ℝ)*X 0 2+(2103511101/5000000000 : ℝ)*X 1 0+(2788652421/5000000000 : ℝ)*X 1 1+(31862133/100000000 : ℝ)*X 1 2+(2103511101/5000000000 : ℝ)*X 2 0+(2788652421/5000000000 : ℝ)*X 2 1+(31862133/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86133553232782830848139/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13935703/100000000000000 : ℝ)*(base1) + (200317637/50000000000000 : ℝ)*(base19) + (6357933/1562500000000 : ℝ)*(base23) + (7466281/20000000000000 : ℝ)*(base24) + (20756081/20000000000000 : ℝ)*(upper3) + (596204122183363/100000000000000 : ℝ)*(major0) + (596204122183363/100000000000000 : ℝ)*(major1) + (596204122183363/100000000000000 : ℝ)*(major2) + (398063685248913/50000000000000 : ℝ)*(sp0) + (159225548006479/20000000000000 : ℝ)*(sp1) + (796127696428551/100000000000000 : ℝ)*(sp2) + (396279325842933/100000000000000 : ℝ)*(sp3) + (156821109/20000000000000 : ℝ)*(sp4) + (1379879/195312500000 : ℝ)*(sp7) + (99070011569171/25000000000000 : ℝ)*(f.failure) + (199032035166917/25000000000000 : ℝ)*(f.sum) + (214636371722429/50000000000000000000000000000 : ℝ)*base66 + (387360620927571/100000000000000000000000000000 : ℝ)*base67 + (321132861572429/100000000000000000000000000000 : ℝ)*base70 + (199439534372429/100000000000000000000000000000 : ℝ)*base72 + (136770288072429/50000000000000000000000000000 : ℝ)*base74 + (611594517772429/100000000000000000000000000000 : ℝ)*base76 + (23144463427571/100000000000000000000000000000 : ℝ)*base77 + (361257915127571/100000000000000000000000000000 : ℝ)*base79 + (470016773322429/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (78921/12500000000000000000 : ℝ)*base89 + (78921/12500000000000000000 : ℝ)*base91 + (78921/12500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (450388338314664761297217/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90999931/100000000000000 : ℝ)*(base1) + (568949603/25000000000000 : ℝ)*(base19) + (1134021803/50000000000000 : ℝ)*(base23) + (245919111/100000000000000 : ℝ)*(upper3) + (13606919/5000000000000 : ℝ)*(upper5) + (629211408343067/100000000000000 : ℝ)*(major0) + (629211408343067/100000000000000 : ℝ)*(major1) + (629211408343067/100000000000000 : ℝ)*(major2) + (4699048291/100000000000000 : ℝ)*(sp1) + (2391661761/50000000000000 : ℝ)*(sp2) + (840203549996159/100000000000000 : ℝ)*(sp4) + (33607859365981/4000000000000 : ℝ)*(sp5) + (8401964076291/1000000000000 : ℝ)*(sp6) + (209109483215539/50000000000000 : ℝ)*(sp7) + (13069345544719/3125000000000 : ℝ)*(f.failure) + (210050864749057/25000000000000 : ℝ)*(f.sum) + (85797075234261/50000000000000000000000000000 : ℝ)*base66 + (276930058865739/100000000000000000000000000000 : ℝ)*base67 + (173676847434261/100000000000000000000000000000 : ℝ)*base70 + (61367552134261/100000000000000000000000000000 : ℝ)*base72 + (123166193815739/50000000000000000000000000000 : ℝ)*base73 + (211808565865739/100000000000000000000000000000 : ℝ)*base75 + (201186543534261/100000000000000000000000000000 : ℝ)*base78 + (414657193065739/100000000000000000000000000000 : ℝ)*base79 + (11375096734261/50000000000000000000000000000 : ℝ)*base82 + (4703/781250000000000000 : ℝ)*base90 + (4703/781250000000000000 : ℝ)*base92 + (4703/781250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1192_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (309/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (221/800 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1192_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077124609/10000000000 : ℝ)*x 0 + (2844179853/5000000000 : ℝ)*x 1 + (2506279379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077124609/10000000000 : ℝ)^8385 ≤ (1562389145657/12500000000000 : ℝ)^6337 := by
    have hnat : (2077124609 : ℕ)^8385*12500000000000^6337 ≤ 1562389145657^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077124609 10000000000 1562389145657 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2844179853/5000000000 : ℝ)^8385 ≤ (47402739833799/100000000000000 : ℝ)^6337 := by
    have hnat : (2844179853 : ℕ)^8385*100000000000000^6337 ≤ 47402739833799^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844179853 5000000000 47402739833799 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506279379/5000000000 : ℝ)^8385 ≤ (1253067093081/3125000000000 : ℝ)^6337 := by
    have hnat : (2506279379 : ℕ)^8385*3125000000000^6337 ≤ 1253067093081^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506279379 5000000000 1253067093081 3125000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077124609/10000000000 : ℝ), (2844179853/5000000000 : ℝ), (2506279379/5000000000 : ℝ)] ![(1562389145657/12500000000000 : ℝ), (47402739833799/100000000000000 : ℝ), (1253067093081/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077124609/10000000000 : ℝ)|^8385 ≤ (1562389145657/12500000000000 : ℝ)^6337
        have hw : |(-2077124609/10000000000 : ℝ)|=(2077124609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2844179853/5000000000 : ℝ)|^8385 ≤ (47402739833799/100000000000000 : ℝ)^6337
        have hw : |(2844179853/5000000000 : ℝ)|=(2844179853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506279379/5000000000 : ℝ)|^8385 ≤ (1253067093081/3125000000000 : ℝ)^6337
        have hw : |(2506279379/5000000000 : ℝ)|=(2506279379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354096503/2500000000 : ℝ)*x 0 + (-2440906629/10000000000 : ℝ)*x 1 + (2506279533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354096503/2500000000 : ℝ)^8385 ≤ (44427259896157/100000000000000 : ℝ)^6337 := by
    have hnat : (1354096503 : ℕ)^8385*100000000000000^6337 ≤ 44427259896157^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354096503 2500000000 44427259896157 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2440906629/10000000000 : ℝ)^8385 ≤ (309491796953/2000000000000 : ℝ)^6337 := by
    have hnat : (2440906629 : ℕ)^8385*2000000000000^6337 ≤ 309491796953^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440906629 10000000000 309491796953 2000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506279533/5000000000 : ℝ)^8385 ≤ (20049075119361/50000000000000 : ℝ)^6337 := by
    have hnat : (2506279533 : ℕ)^8385*50000000000000^6337 ≤ 20049075119361^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506279533 5000000000 20049075119361 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354096503/2500000000 : ℝ), (-2440906629/10000000000 : ℝ), (2506279533/5000000000 : ℝ)] ![(44427259896157/100000000000000 : ℝ), (309491796953/2000000000000 : ℝ), (20049075119361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354096503/2500000000 : ℝ)|^8385 ≤ (44427259896157/100000000000000 : ℝ)^6337
        have hw : |(1354096503/2500000000 : ℝ)|=(1354096503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2440906629/10000000000 : ℝ)|^8385 ≤ (309491796953/2000000000000 : ℝ)^6337
        have hw : |(-2440906629/10000000000 : ℝ)|=(2440906629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506279533/5000000000 : ℝ)|^8385 ≤ (20049075119361/50000000000000 : ℝ)^6337
        have hw : |(2506279533/5000000000 : ℝ)|=(2506279533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (169262033/312500000 : ℝ)*x 0 + (1253139923/2500000000 : ℝ)*x 1 + (-610226769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169262033/312500000 : ℝ)^8385 ≤ (44427249520463/100000000000000 : ℝ)^6337 := by
    have hnat : (169262033 : ℕ)^8385*100000000000000^6337 ≤ 44427249520463^6337*312500000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169262033 312500000 44427249520463 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253139923/2500000000 : ℝ)^8385 ≤ (40098156864831/100000000000000 : ℝ)^6337 := by
    have hnat : (1253139923 : ℕ)^8385*100000000000000^6337 ≤ 40098156864831^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253139923 2500000000 40098156864831 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610226769/2500000000 : ℝ)^8385 ≤ (1934324199667/12500000000000 : ℝ)^6337 := by
    have hnat : (610226769 : ℕ)^8385*12500000000000^6337 ≤ 1934324199667^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610226769 2500000000 1934324199667 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169262033/312500000 : ℝ), (1253139923/2500000000 : ℝ), (-610226769/2500000000 : ℝ)] ![(44427249520463/100000000000000 : ℝ), (40098156864831/100000000000000 : ℝ), (1934324199667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169262033/312500000 : ℝ)|^8385 ≤ (44427249520463/100000000000000 : ℝ)^6337
        have hw : |(169262033/312500000 : ℝ)|=(169262033/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1253139923/2500000000 : ℝ)|^8385 ≤ (40098156864831/100000000000000 : ℝ)^6337
        have hw : |(1253139923/2500000000 : ℝ)|=(1253139923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-610226769/2500000000 : ℝ)|^8385 ≤ (1934324199667/12500000000000 : ℝ)^6337
        have hw : |(-610226769/2500000000 : ℝ)|=(610226769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4313171311/10000000000 : ℝ)*x 0 + (1843162947/5000000000 : ℝ)*x 1 + (5044012951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313171311/10000000000 : ℝ)^8385 ≤ (32867738820527/100000000000000 : ℝ)^6337 := by
    have hnat : (4313171311 : ℕ)^8385*100000000000000^6337 ≤ 32867738820527^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313171311 10000000000 32867738820527 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1843162947/5000000000 : ℝ)^8385 ≤ (83440123619/312500000000 : ℝ)^6337 := by
    have hnat : (1843162947 : ℕ)^8385*312500000000^6337 ≤ 83440123619^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843162947 5000000000 83440123619 312500000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5044012951/10000000000 : ℝ)^8385 ≤ (20215710806847/50000000000000 : ℝ)^6337 := by
    have hnat : (5044012951 : ℕ)^8385*50000000000000^6337 ≤ 20215710806847^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044012951 10000000000 20215710806847 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313171311/10000000000 : ℝ), (1843162947/5000000000 : ℝ), (5044012951/10000000000 : ℝ)] ![(32867738820527/100000000000000 : ℝ), (83440123619/312500000000 : ℝ), (20215710806847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313171311/10000000000 : ℝ)|^8385 ≤ (32867738820527/100000000000000 : ℝ)^6337
        have hw : |(4313171311/10000000000 : ℝ)|=(4313171311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1843162947/5000000000 : ℝ)|^8385 ≤ (83440123619/312500000000 : ℝ)^6337
        have hw : |(1843162947/5000000000 : ℝ)|=(1843162947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5044012951/10000000000 : ℝ)|^8385 ≤ (20215710806847/50000000000000 : ℝ)^6337
        have hw : |(5044012951/10000000000 : ℝ)|=(5044012951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-415572647/2000000000 : ℝ)*x 0 + (5021611049/10000000000 : ℝ)*x 1 + (1419782903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415572647/2000000000 : ℝ)^8385 ≤ (2500998926147/20000000000000 : ℝ)^6337 := by
    have hnat : (415572647 : ℕ)^8385*20000000000000^6337 ≤ 2500998926147^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415572647 2000000000 2500998926147 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5021611049/10000000000 : ℝ)^8385 ≤ (20096995977971/50000000000000 : ℝ)^6337 := by
    have hnat : (5021611049 : ℕ)^8385*50000000000000^6337 ≤ 20096995977971^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021611049 10000000000 20096995977971 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419782903/2500000000 : ℝ)^8385 ≤ (378408107129/800000000000 : ℝ)^6337 := by
    have hnat : (1419782903 : ℕ)^8385*800000000000^6337 ≤ 378408107129^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419782903 2500000000 378408107129 800000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415572647/2000000000 : ℝ), (5021611049/10000000000 : ℝ), (1419782903/2500000000 : ℝ)] ![(2500998926147/20000000000000 : ℝ), (20096995977971/50000000000000 : ℝ), (378408107129/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415572647/2000000000 : ℝ)|^8385 ≤ (2500998926147/20000000000000 : ℝ)^6337
        have hw : |(-415572647/2000000000 : ℝ)|=(415572647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5021611049/10000000000 : ℝ)|^8385 ≤ (20096995977971/50000000000000 : ℝ)^6337
        have hw : |(5021611049/10000000000 : ℝ)|=(5021611049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419782903/2500000000 : ℝ)|^8385 ≤ (378408107129/800000000000 : ℝ)^6337
        have hw : |(1419782903/2500000000 : ℝ)|=(1419782903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2621347203/5000000000 : ℝ)*x 0 + (-1774333913/10000000000 : ℝ)*x 1 + (1419782993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621347203/5000000000 : ℝ)^8385 ≤ (8510396760023/20000000000000 : ℝ)^6337 := by
    have hnat : (2621347203 : ℕ)^8385*20000000000000^6337 ≤ 8510396760023^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621347203 5000000000 8510396760023 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774333913/10000000000 : ℝ)^8385 ≤ (2536749708657/25000000000000 : ℝ)^6337 := by
    have hnat : (1774333913 : ℕ)^8385*25000000000000^6337 ≤ 2536749708657^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774333913 10000000000 2536749708657 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419782993/2500000000 : ℝ)^8385 ≤ (9460203471713/20000000000000 : ℝ)^6337 := by
    have hnat : (1419782993 : ℕ)^8385*20000000000000^6337 ≤ 9460203471713^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419782993 2500000000 9460203471713 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621347203/5000000000 : ℝ), (-1774333913/10000000000 : ℝ), (1419782993/2500000000 : ℝ)] ![(8510396760023/20000000000000 : ℝ), (2536749708657/25000000000000 : ℝ), (9460203471713/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621347203/5000000000 : ℝ)|^8385 ≤ (8510396760023/20000000000000 : ℝ)^6337
        have hw : |(2621347203/5000000000 : ℝ)|=(2621347203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1774333913/10000000000 : ℝ)|^8385 ≤ (2536749708657/25000000000000 : ℝ)^6337
        have hw : |(-1774333913/10000000000 : ℝ)|=(1774333913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419782993/2500000000 : ℝ)|^8385 ≤ (9460203471713/20000000000000 : ℝ)^6337
        have hw : |(1419782993/2500000000 : ℝ)|=(1419782993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5242694307/10000000000 : ℝ)*x 0 + (2839566331/5000000000 : ℝ)*x 1 + (-221791631/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242694307/10000000000 : ℝ)^8385 ≤ (42551982736903/100000000000000 : ℝ)^6337 := by
    have hnat : (5242694307 : ℕ)^8385*100000000000000^6337 ≤ 42551982736903^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242694307 10000000000 42551982736903 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2839566331/5000000000 : ℝ)^8385 ≤ (1892040998513/4000000000000 : ℝ)^6337 := by
    have hnat : (2839566331 : ℕ)^8385*4000000000000^6337 ≤ 1892040998513^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839566331 5000000000 1892040998513 4000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (221791631/1250000000 : ℝ)^8385 ≤ (2029398457841/20000000000000 : ℝ)^6337 := by
    have hnat : (221791631 : ℕ)^8385*20000000000000^6337 ≤ 2029398457841^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221791631 1250000000 2029398457841 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242694307/10000000000 : ℝ), (2839566331/5000000000 : ℝ), (-221791631/1250000000 : ℝ)] ![(42551982736903/100000000000000 : ℝ), (1892040998513/4000000000000 : ℝ), (2029398457841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242694307/10000000000 : ℝ)|^8385 ≤ (42551982736903/100000000000000 : ℝ)^6337
        have hw : |(5242694307/10000000000 : ℝ)|=(5242694307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2839566331/5000000000 : ℝ)|^8385 ≤ (1892040998513/4000000000000 : ℝ)^6337
        have hw : |(2839566331/5000000000 : ℝ)|=(2839566331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-221791631/1250000000 : ℝ)|^8385 ≤ (2029398457841/20000000000000 : ℝ)^6337
        have hw : |(-221791631/1250000000 : ℝ)|=(221791631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s1_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4314654317/10000000000 : ℝ)*x 0 + (2512913521/5000000000 : ℝ)*x 1 + (740972861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314654317/10000000000 : ℝ)^8385 ≤ (16441346447071/50000000000000 : ℝ)^6337 := by
    have hnat : (4314654317 : ℕ)^8385*50000000000000^6337 ≤ 16441346447071^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314654317 10000000000 16441346447071 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512913521/5000000000 : ℝ)^8385 ≤ (10059662410469/25000000000000 : ℝ)^6337 := by
    have hnat : (2512913521 : ℕ)^8385*25000000000000^6337 ≤ 10059662410469^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512913521 5000000000 10059662410469 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740972861/2000000000 : ℝ)^8385 ≤ (6719664360357/25000000000000 : ℝ)^6337 := by
    have hnat : (740972861 : ℕ)^8385*25000000000000^6337 ≤ 6719664360357^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740972861 2000000000 6719664360357 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314654317/10000000000 : ℝ), (2512913521/5000000000 : ℝ), (740972861/2000000000 : ℝ)] ![(16441346447071/50000000000000 : ℝ), (10059662410469/25000000000000 : ℝ), (6719664360357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314654317/10000000000 : ℝ)|^8385 ≤ (16441346447071/50000000000000 : ℝ)^6337
        have hw : |(4314654317/10000000000 : ℝ)|=(4314654317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2512913521/5000000000 : ℝ)|^8385 ≤ (10059662410469/25000000000000 : ℝ)^6337
        have hw : |(2512913521/5000000000 : ℝ)|=(2512913521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(740972861/2000000000 : ℝ)|^8385 ≤ (6719664360357/25000000000000 : ℝ)^6337
        have hw : |(740972861/2000000000 : ℝ)|=(740972861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (221/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (237/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10107/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (221/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (309/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (221/800 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (309/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (221/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (309/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (221/800 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (309/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (221/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (309/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (221/800 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (309/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (309/50000 : ℝ) ^ (131/32 : ℝ) ≤ (90543873513/100000000000000000000 : ℝ) := by
    have hpowers : (309/50000 : ℝ)^131 ≤ (90543873513/100000000000000000000 : ℝ)^32 := by
      have hnat : (309 : ℕ)^131*100000000000000000000^32 ≤ 90543873513^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        309 50000 90543873513 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (309/50000 : ℝ)) (X := (90543873513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (221/800 : ℝ) ^ (131/32 : ℝ) ≤ (516215732406966923/100000000000000000000 : ℝ) := by
    have hpowers : (221/800 : ℝ)^131 ≤ (516215732406966923/100000000000000000000 : ℝ)^32 := by
      have hnat : (221 : ℕ)^131*100000000000000000000^32 ≤ 516215732406966923^32*800^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        221 800 516215732406966923 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (221/800 : ℝ)) (X := (516215732406966923/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000090543873513/50000000000000000000 : ℝ) ≤ (5000000002211759/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50000000090543873513/50000000000000000000 : ℝ)^32 ≤ (5000000002211759/5000000000000000 : ℝ)^131 := by
      have hnat : (50000000090543873513 : ℕ)^32*5000000000000000^131 ≤ 5000000002211759^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000090543873513 50000000000000000000 5000000002211759 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000002211759/5000000000000000 : ℝ)) (X := (50000000090543873513/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (25129053955737710109/25000000000000000000 : ℝ) ≤ (5006292664801011/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25129053955737710109/25000000000000000000 : ℝ)^32 ≤ (5006292664801011/5000000000000000 : ℝ)^131 := by
      have hnat : (25129053955737710109 : ℕ)^32*5000000000000000^131 ≤ 5006292664801011^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25129053955737710109 25000000000000000000 5006292664801011 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006292664801011/5000000000000000 : ℝ)) (X := (25129053955737710109/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50516215732406966923/50000000000000000000 : ℝ) ≤ (5012585327390263/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50516215732406966923/50000000000000000000 : ℝ)^32 ≤ (5012585327390263/5000000000000000 : ℝ)^131 := by
      have hnat : (50516215732406966923 : ℕ)^32*5000000000000000^131 ≤ 5012585327390263^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50516215732406966923 50000000000000000000 5012585327390263 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012585327390263/5000000000000000 : ℝ)) (X := (50516215732406966923/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(90543873513/100000000000000000000 : ℝ) ≤ ((135027222328772659841/135035000000000000000 : ℝ)+2*(1573165647313/337587500000000 : ℝ)*(309/50000 : ℝ))^(131/32 : ℝ) := by
    rw [show (135027222328772659841/135035000000000000000 : ℝ)+2*(1573165647313/337587500000000 : ℝ)*(309/50000 : ℝ)=(5000000002211759/5000000000000000 : ℝ) by norm_num, show 1+2*(90543873513/100000000000000000000 : ℝ)=(50000000090543873513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(516215732406966923/100000000000000000000 : ℝ)+(90543873513/100000000000000000000 : ℝ) ≤ ((135027222328772659841/135035000000000000000 : ℝ)+(1573165647313/337587500000000 : ℝ)*((221/800 : ℝ)+(309/50000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (135027222328772659841/135035000000000000000 : ℝ)+(1573165647313/337587500000000 : ℝ)*((221/800 : ℝ)+(309/50000 : ℝ))=(5006292664801011/5000000000000000 : ℝ) by norm_num, show 1+(516215732406966923/100000000000000000000 : ℝ)+(90543873513/100000000000000000000 : ℝ)=(25129053955737710109/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(516215732406966923/100000000000000000000 : ℝ) ≤ ((135027222328772659841/135035000000000000000 : ℝ)+2*(1573165647313/337587500000000 : ℝ)*(221/800 : ℝ))^(131/32 : ℝ) := by
    rw [show (135027222328772659841/135035000000000000000 : ℝ)+2*(1573165647313/337587500000000 : ℝ)*(221/800 : ℝ)=(5012585327390263/5000000000000000 : ℝ) by norm_num, show 1+2*(516215732406966923/100000000000000000000 : ℝ)=(50516215732406966923/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (135027222328772659841/135035000000000000000 : ℝ)*(X 1 0+X 2 0)+(1573165647313/337587500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (309/50000 : ℝ)) (hi := (221/800 : ℝ)) (c := (135027222328772659841/135035000000000000000 : ℝ)) (alpha := (1573165647313/337587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (135027222328772659841/135035000000000000000 : ℝ)*(X 0 1+X 2 1)+(1573165647313/337587500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (309/50000 : ℝ)) (hi := (221/800 : ℝ)) (c := (135027222328772659841/135035000000000000000 : ℝ)) (alpha := (1573165647313/337587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (135027222328772659841/135035000000000000000 : ℝ)*(X 0 2+X 1 2)+(1573165647313/337587500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (309/50000 : ℝ)) (hi := (221/800 : ℝ)) (c := (135027222328772659841/135035000000000000000 : ℝ)) (alpha := (1573165647313/337587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077124609/10000000000 : ℝ)*X 0 0+(2844179853/5000000000 : ℝ)*X 0 1+(2506279379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354096503/2500000000 : ℝ)*X 1 0+(-2440906629/10000000000 : ℝ)*X 1 1+(2506279533/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((169262033/312500000 : ℝ)*X 2 0+(1253139923/2500000000 : ℝ)*X 2 1+(-610226769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313171311/10000000000 : ℝ)*X 0 0+(1843162947/5000000000 : ℝ)*X 0 1+(5044012951/10000000000 : ℝ)*X 0 2+(4313171311/10000000000 : ℝ)*X 1 0+(1843162947/5000000000 : ℝ)*X 1 1+(5044012951/10000000000 : ℝ)*X 1 2+(4313171311/10000000000 : ℝ)*X 2 0+(1843162947/5000000000 : ℝ)*X 2 1+(5044012951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415572647/2000000000 : ℝ)*X 0 0+(5021611049/10000000000 : ℝ)*X 0 1+(1419782903/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2621347203/5000000000 : ℝ)*X 1 0+(-1774333913/10000000000 : ℝ)*X 1 1+(1419782993/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5242694307/10000000000 : ℝ)*X 2 0+(2839566331/5000000000 : ℝ)*X 2 1+(-221791631/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314654317/10000000000 : ℝ)*X 0 0+(2512913521/5000000000 : ℝ)*X 0 1+(740972861/2000000000 : ℝ)*X 0 2+(4314654317/10000000000 : ℝ)*X 1 0+(2512913521/5000000000 : ℝ)*X 1 1+(740972861/2000000000 : ℝ)*X 1 2+(4314654317/10000000000 : ℝ)*X 2 0+(2512913521/5000000000 : ℝ)*X 2 1+(740972861/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186319445579157601115451/67517500000000000000000000000 : ℝ) := by norm_num
    linear_combination (56779/1562500000000 : ℝ)*(base16) + (788592089/100000000000000 : ℝ)*(base19) + (290404569/50000000000000 : ℝ)*(base23) + (13475591/50000000000000 : ℝ)*(upper2) + (90319893/50000000000000 : ℝ)*(upper3) + (1108143926359181/100000000000000 : ℝ)*(major0) + (1108143926359181/100000000000000 : ℝ)*(major1) + (1108143926359181/100000000000000 : ℝ)*(major2) + (1479731934323017/100000000000000 : ℝ)*(sp0) + (1479734988941871/100000000000000 : ℝ)*(sp1) + (739867600179339/50000000000000 : ℝ)*(sp2) + (14730981691163/2000000000000 : ℝ)*(sp3) + (1923422399/50000000000000 : ℝ)*(sp4) + (2895006637/100000000000000 : ℝ)*(sp7) + (736551979564787/100000000000000 : ℝ)*(f.failure) + (184966972645977/12500000000000 : ℝ)*(f.sum) + (106693646444267/16879375000000000000000000000 : ℝ)*base66 + (69048933157908550221/13503500000000000000000000000000000 : ℝ)*base67 + (9297566859427949779/13503500000000000000000000000000000 : ℝ)*base70 + (25725450095346949779/13503500000000000000000000000000000 : ℝ)*base72 + (578856021135399/135035000000000000000000000000 : ℝ)*base73 + (34127458038288050221/13503500000000000000000000000000000 : ℝ)*base75 + (87755229187652949779/13503500000000000000000000000000000 : ℝ)*base78 + (20853846902156550221/13503500000000000000000000000000000 : ℝ)*base79 + (464361788259021/135035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (85537/50000000000000000000 : ℝ)*base89 + (85537/50000000000000000000 : ℝ)*base91 + (85537/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5433394894761416578179077559/6751750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (676466613/100000000000000 : ℝ)*(base19) + (480670357/50000000000000 : ℝ)*(base23) + (10978723/10000000000000 : ℝ)*(upper2) + (121625811/100000000000000 : ℝ)*(upper3) + (67142723/100000000000000 : ℝ)*(upper5) + (1138943865387133/100000000000000 : ℝ)*(major0) + (1138943865387133/100000000000000 : ℝ)*(major1) + (1138943865387133/100000000000000 : ℝ)*(major2) + (3381739369/100000000000000 : ℝ)*(sp1) + (1631607801/25000000000000 : ℝ)*(sp2) + (760431937272431/50000000000000 : ℝ)*(sp4) + (760429908169441/50000000000000 : ℝ)*(sp5) + (304171277354589/20000000000000 : ℝ)*(sp6) + (23656994668899/3125000000000 : ℝ)*(sp7) + (23656994668899/3125000000000 : ℝ)*(f.failure) + (760431937272431/50000000000000 : ℝ)*(f.sum) + (213467826479011/67517500000000000000000000000 : ℝ)*base65 + (23095848165690174147/13503500000000000000000000000000000 : ℝ)*base68 + (124256135883794825853/13503500000000000000000000000000000 : ℝ)*base69 + (42724096658877174147/13503500000000000000000000000000000 : ℝ)*base72 + (167800921887917/135035000000000000000000000000 : ℝ)*base73 + (115925583350104174147/13503500000000000000000000000000000 : ℝ)*base76 + (56286117246056325853/13503500000000000000000000000000000 : ℝ)*base77 + (72295560360510174147/13503500000000000000000000000000000 : ℝ)*base80 + (20009997478621/4219843750000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2869/390625000000000000 : ℝ)*base90 + (2869/390625000000000000 : ℝ)*base92 + (2869/390625000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1192_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (221/800 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (237/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10107/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1192_s2_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063861449/5000000000 : ℝ)*x 0 + (220061793/400000000 : ℝ)*x 1 + (5167151477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063861449/5000000000 : ℝ)^8385 ≤ (12903566796529/100000000000000 : ℝ)^6337 := by
    have hnat : (1063861449 : ℕ)^8385*100000000000000^6337 ≤ 12903566796529^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063861449 5000000000 12903566796529 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220061793/400000000 : ℝ)^8385 ≤ (11338462133597/25000000000000 : ℝ)^6337 := by
    have hnat : (220061793 : ℕ)^8385*25000000000000^6337 ≤ 11338462133597^6337*400000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220061793 400000000 11338462133597 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167151477/10000000000 : ℝ)^8385 ≤ (20871292322049/50000000000000 : ℝ)^6337 := by
    have hnat : (5167151477 : ℕ)^8385*50000000000000^6337 ≤ 20871292322049^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167151477 10000000000 20871292322049 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063861449/5000000000 : ℝ), (220061793/400000000 : ℝ), (5167151477/10000000000 : ℝ)] ![(12903566796529/100000000000000 : ℝ), (11338462133597/25000000000000 : ℝ), (20871292322049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063861449/5000000000 : ℝ)|^8385 ≤ (12903566796529/100000000000000 : ℝ)^6337
        have hw : |(-1063861449/5000000000 : ℝ)|=(1063861449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220061793/400000000 : ℝ)|^8385 ≤ (11338462133597/25000000000000 : ℝ)^6337
        have hw : |(220061793/400000000 : ℝ)|=(220061793/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167151477/10000000000 : ℝ)|^8385 ≤ (20871292322049/50000000000000 : ℝ)^6337
        have hw : |(5167151477/10000000000 : ℝ)|=(5167151477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537174277/1000000000 : ℝ)*x 0 + (-460248597/2000000000 : ℝ)*x 1 + (5167155579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537174277/1000000000 : ℝ)^8385 ≤ (10985845686199/25000000000000 : ℝ)^6337 := by
    have hnat : (537174277 : ℕ)^8385*25000000000000^6337 ≤ 10985845686199^6337*1000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537174277 1000000000 10985845686199 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460248597/2000000000 : ℝ)^8385 ≤ (14313988746607/100000000000000 : ℝ)^6337 := by
    have hnat : (460248597 : ℕ)^8385*100000000000000^6337 ≤ 14313988746607^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460248597 2000000000 14313988746607 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167155579/10000000000 : ℝ)^8385 ≤ (20871314245717/50000000000000 : ℝ)^6337 := by
    have hnat : (5167155579 : ℕ)^8385*50000000000000^6337 ≤ 20871314245717^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167155579 10000000000 20871314245717 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537174277/1000000000 : ℝ), (-460248597/2000000000 : ℝ), (5167155579/10000000000 : ℝ)] ![(10985845686199/25000000000000 : ℝ), (14313988746607/100000000000000 : ℝ), (20871314245717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537174277/1000000000 : ℝ)|^8385 ≤ (10985845686199/25000000000000 : ℝ)^6337
        have hw : |(537174277/1000000000 : ℝ)|=(537174277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460248597/2000000000 : ℝ)|^8385 ≤ (14313988746607/100000000000000 : ℝ)^6337
        have hw : |(-460248597/2000000000 : ℝ)|=(460248597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167155579/10000000000 : ℝ)|^8385 ≤ (20871314245717/50000000000000 : ℝ)^6337
        have hw : |(5167155579/10000000000 : ℝ)|=(5167155579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (335734027/625000000 : ℝ)*x 0 + (5167153247/10000000000 : ℝ)*x 1 + (-575310957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335734027/625000000 : ℝ)^8385 ≤ (43943400734693/100000000000000 : ℝ)^6337 := by
    have hnat : (335734027 : ℕ)^8385*100000000000000^6337 ≤ 43943400734693^6337*625000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335734027 625000000 43943400734693 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167153247/10000000000 : ℝ)^8385 ≤ (41742603564083/100000000000000 : ℝ)^6337 := by
    have hnat : (5167153247 : ℕ)^8385*100000000000000^6337 ≤ 41742603564083^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167153247 10000000000 41742603564083 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575310957/2500000000 : ℝ)^8385 ≤ (14313995684781/100000000000000 : ℝ)^6337 := by
    have hnat : (575310957 : ℕ)^8385*100000000000000^6337 ≤ 14313995684781^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575310957 2500000000 14313995684781 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335734027/625000000 : ℝ), (5167153247/10000000000 : ℝ), (-575310957/2500000000 : ℝ)] ![(43943400734693/100000000000000 : ℝ), (41742603564083/100000000000000 : ℝ), (14313995684781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335734027/625000000 : ℝ)|^8385 ≤ (43943400734693/100000000000000 : ℝ)^6337
        have hw : |(335734027/625000000 : ℝ)|=(335734027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167153247/10000000000 : ℝ)|^8385 ≤ (41742603564083/100000000000000 : ℝ)^6337
        have hw : |(5167153247/10000000000 : ℝ)|=(5167153247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-575310957/2500000000 : ℝ)|^8385 ≤ (14313995684781/100000000000000 : ℝ)^6337
        have hw : |(-575310957/2500000000 : ℝ)|=(575310957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869600591/2000000000 : ℝ)*x 0 + (2012408697/5000000000 : ℝ)*x 1 + (4696610769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869600591/2000000000 : ℝ)^8385 ≤ (6643881191729/20000000000000 : ℝ)^6337 := by
    have hnat : (869600591 : ℕ)^8385*20000000000000^6337 ≤ 6643881191729^6337*2000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869600591 2000000000 6643881191729 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012408697/5000000000 : ℝ)^8385 ≤ (7498036332953/25000000000000 : ℝ)^6337 := by
    have hnat : (2012408697 : ℕ)^8385*25000000000000^6337 ≤ 7498036332953^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012408697 5000000000 7498036332953 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4696610769/10000000000 : ℝ)^8385 ≤ (36788448698503/100000000000000 : ℝ)^6337 := by
    have hnat : (4696610769 : ℕ)^8385*100000000000000^6337 ≤ 36788448698503^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696610769 10000000000 36788448698503 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869600591/2000000000 : ℝ), (2012408697/5000000000 : ℝ), (4696610769/10000000000 : ℝ)] ![(6643881191729/20000000000000 : ℝ), (7498036332953/25000000000000 : ℝ), (36788448698503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869600591/2000000000 : ℝ)|^8385 ≤ (6643881191729/20000000000000 : ℝ)^6337
        have hw : |(869600591/2000000000 : ℝ)|=(869600591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012408697/5000000000 : ℝ)|^8385 ≤ (7498036332953/25000000000000 : ℝ)^6337
        have hw : |(2012408697/5000000000 : ℝ)|=(2012408697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4696610769/10000000000 : ℝ)|^8385 ≤ (36788448698503/100000000000000 : ℝ)^6337
        have hw : |(4696610769/10000000000 : ℝ)|=(4696610769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_4 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-4255623/20000000 : ℝ)*x 0 + (1292344733/2500000000 : ℝ)*x 1 + (2749648289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255623/20000000 : ℝ)^8385 ≤ (6452138890827/50000000000000 : ℝ)^6337 := by
    have hnat : (4255623 : ℕ)^8385*50000000000000^6337 ≤ 6452138890827^6337*20000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255623 20000000 6452138890827 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292344733/2500000000 : ℝ)^8385 ≤ (20883198070289/50000000000000 : ℝ)^6337 := by
    have hnat : (1292344733 : ℕ)^8385*50000000000000^6337 ≤ 20883198070289^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292344733 2500000000 20883198070289 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749648289/5000000000 : ℝ)^8385 ≤ (45329326065647/100000000000000 : ℝ)^6337 := by
    have hnat : (2749648289 : ℕ)^8385*100000000000000^6337 ≤ 45329326065647^6337*5000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749648289 5000000000 45329326065647 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4255623/20000000 : ℝ), (1292344733/2500000000 : ℝ), (2749648289/5000000000 : ℝ)] ![(6452138890827/50000000000000 : ℝ), (20883198070289/50000000000000 : ℝ), (45329326065647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4255623/20000000 : ℝ)|^8385 ≤ (6452138890827/50000000000000 : ℝ)^6337
        have hw : |(-4255623/20000000 : ℝ)|=(4255623/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292344733/2500000000 : ℝ)|^8385 ≤ (20883198070289/50000000000000 : ℝ)^6337
        have hw : |(1292344733/2500000000 : ℝ)|=(1292344733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749648289/5000000000 : ℝ)|^8385 ≤ (45329326065647/100000000000000 : ℝ)^6337
        have hw : |(2749648289/5000000000 : ℝ)|=(2749648289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (660827513/1250000000 : ℝ)*x 0 + (-61534387/312500000 : ℝ)*x 1 + (5499296593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660827513/1250000000 : ℝ)^8385 ≤ (43024361925869/100000000000000 : ℝ)^6337 := by
    have hnat : (660827513 : ℕ)^8385*100000000000000^6337 ≤ 43024361925869^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660827513 1250000000 43024361925869 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61534387/312500000 : ℝ)^8385 ≤ (5823155913579/50000000000000 : ℝ)^6337 := by
    have hnat : (61534387 : ℕ)^8385*50000000000000^6337 ≤ 5823155913579^6337*312500000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61534387 312500000 5823155913579 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499296593/10000000000 : ℝ)^8385 ≤ (45329326229247/100000000000000 : ℝ)^6337 := by
    have hnat : (5499296593 : ℕ)^8385*100000000000000^6337 ≤ 45329326229247^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499296593 10000000000 45329326229247 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660827513/1250000000 : ℝ), (-61534387/312500000 : ℝ), (5499296593/10000000000 : ℝ)] ![(43024361925869/100000000000000 : ℝ), (5823155913579/50000000000000 : ℝ), (45329326229247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660827513/1250000000 : ℝ)|^8385 ≤ (43024361925869/100000000000000 : ℝ)^6337
        have hw : |(660827513/1250000000 : ℝ)|=(660827513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61534387/312500000 : ℝ)|^8385 ≤ (5823155913579/50000000000000 : ℝ)^6337
        have hw : |(-61534387/312500000 : ℝ)|=(61534387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499296593/10000000000 : ℝ)|^8385 ≤ (45329326229247/100000000000000 : ℝ)^6337
        have hw : |(5499296593/10000000000 : ℝ)|=(5499296593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321655067/2500000000 : ℝ)*x 0 + (1374824151/2500000000 : ℝ)*x 1 + (-1969100143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321655067/2500000000 : ℝ)^8385 ≤ (8604872738381/20000000000000 : ℝ)^6337 := by
    have hnat : (1321655067 : ℕ)^8385*20000000000000^6337 ≤ 8604872738381^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321655067 2500000000 8604872738381 20000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374824151/2500000000 : ℝ)^8385 ≤ (2266466317461/5000000000000 : ℝ)^6337 := by
    have hnat : (1374824151 : ℕ)^8385*5000000000000^6337 ≤ 2266466317461^6337*2500000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374824151 2500000000 2266466317461 5000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1969100143/10000000000 : ℝ)^8385 ≤ (2911577485273/25000000000000 : ℝ)^6337 := by
    have hnat : (1969100143 : ℕ)^8385*25000000000000^6337 ≤ 2911577485273^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969100143 10000000000 2911577485273 25000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321655067/2500000000 : ℝ), (1374824151/2500000000 : ℝ), (-1969100143/10000000000 : ℝ)] ![(8604872738381/20000000000000 : ℝ), (2266466317461/5000000000000 : ℝ), (2911577485273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321655067/2500000000 : ℝ)|^8385 ≤ (8604872738381/20000000000000 : ℝ)^6337
        have hw : |(1321655067/2500000000 : ℝ)|=(1321655067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374824151/2500000000 : ℝ)|^8385 ≤ (2266466317461/5000000000000 : ℝ)^6337
        have hw : |(1374824151/2500000000 : ℝ)|=(1374824151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1969100143/10000000000 : ℝ)|^8385 ≤ (2911577485273/25000000000000 : ℝ)^6337
        have hw : |(-1969100143/10000000000 : ℝ)|=(1969100143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1192_s2_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348183161/10000000000 : ℝ)*x 0 + (586517313/1250000000 : ℝ)*x 1 + (100733303/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348183161/10000000000 : ℝ)^8385 ≤ (4152653466081/12500000000000 : ℝ)^6337 := by
    have hnat : (4348183161 : ℕ)^8385*12500000000000^6337 ≤ 4152653466081^6337*10000000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348183161 10000000000 4152653466081 12500000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586517313/1250000000 : ℝ)^8385 ≤ (18371051632477/50000000000000 : ℝ)^6337 := by
    have hnat : (586517313 : ℕ)^8385*50000000000000^6337 ≤ 18371051632477^6337*1250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586517313 1250000000 18371051632477 50000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100733303/250000000 : ℝ)^8385 ≤ (30036668986061/100000000000000 : ℝ)^6337 := by
    have hnat : (100733303 : ℕ)^8385*100000000000000^6337 ≤ 30036668986061^6337*250000000^8385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100733303 250000000 30036668986061 100000000000000 8385 6337 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8385/2048 : ℝ)) 8385 6337 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348183161/10000000000 : ℝ), (586517313/1250000000 : ℝ), (100733303/250000000 : ℝ)] ![(4152653466081/12500000000000 : ℝ), (18371051632477/50000000000000 : ℝ), (30036668986061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348183161/10000000000 : ℝ)|^8385 ≤ (4152653466081/12500000000000 : ℝ)^6337
        have hw : |(4348183161/10000000000 : ℝ)|=(4348183161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586517313/1250000000 : ℝ)|^8385 ≤ (18371051632477/50000000000000 : ℝ)^6337
        have hw : |(586517313/1250000000 : ℝ)|=(586517313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100733303/250000000 : ℝ)|^8385 ≤ (30036668986061/100000000000000 : ℝ)^6337
        have hw : |(100733303/250000000 : ℝ)|=(100733303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1192_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10107/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (237/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (9291/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8179/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10107/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (237/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10107/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (237/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10107/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (237/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10107/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (237/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10107/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (237/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10107/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (237/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (237/4000 : ℝ) ^ (131/32 : ℝ) ≤ (189113680831891/20000000000000000000 : ℝ) := by
    have hpowers : (237/4000 : ℝ)^131 ≤ (189113680831891/20000000000000000000 : ℝ)^32 := by
      have hnat : (237 : ℕ)^131*20000000000000000000^32 ≤ 189113680831891^32*4000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        237 4000 189113680831891 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (237/4000 : ℝ)) (X := (189113680831891/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hpowhi : (10107/50000 : ℝ) ^ (131/32 : ℝ) ≤ (71859459999349221/50000000000000000000 : ℝ) := by
    have hpowers : (10107/50000 : ℝ)^131 ≤ (71859459999349221/50000000000000000000 : ℝ)^32 := by
      have hnat : (10107 : ℕ)^131*50000000000000000000^32 ≤ 71859459999349221^32*50000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10107 50000 71859459999349221 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10107/50000 : ℝ)) (X := (71859459999349221/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000189113680831891/10000000000000000000 : ℝ) ≤ (10000046195378189/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (10000189113680831891/10000000000000000000 : ℝ)^32 ≤ (10000046195378189/10000000000000000 : ℝ)^131 := by
      have hnat : (10000189113680831891 : ℕ)^32*10000000000000000^131 ≤ 10000046195378189^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000189113680831891 10000000000000000000 10000046195378189 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000046195378189/10000000000000000 : ℝ)) (X := (10000189113680831891/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100144664488402857897/100000000000000000000 : ℝ) ≤ (1250441482372229/1250000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100144664488402857897/100000000000000000000 : ℝ)^32 ≤ (1250441482372229/1250000000000000 : ℝ)^131 := by
      have hnat : (100144664488402857897 : ℕ)^32*1250000000000000^131 ≤ 1250441482372229^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100144664488402857897 100000000000000000000 1250441482372229 1250000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250441482372229/1250000000000000 : ℝ)) (X := (100144664488402857897/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25071859459999349221/25000000000000000000 : ℝ) ≤ (400280700903099/400000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25071859459999349221/25000000000000000000 : ℝ)^32 ≤ (400280700903099/400000000000000 : ℝ)^131 := by
      have hnat : (25071859459999349221 : ℕ)^32*400000000000000^131 ≤ 400280700903099^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25071859459999349221 25000000000000000000 400280700903099 400000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400280700903099/400000000000000 : ℝ)) (X := (25071859459999349221/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(189113680831891/20000000000000000000 : ℝ) ≤ ((47616451657367724357/47630000000000000000 : ℝ)+2*(3485663599643/1428900000000000 : ℝ)*(237/4000 : ℝ))^(131/32 : ℝ) := by
    rw [show (47616451657367724357/47630000000000000000 : ℝ)+2*(3485663599643/1428900000000000 : ℝ)*(237/4000 : ℝ)=(10000046195378189/10000000000000000 : ℝ) by norm_num, show 1+2*(189113680831891/20000000000000000000 : ℝ)=(10000189113680831891/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71859459999349221/50000000000000000000 : ℝ)+(189113680831891/20000000000000000000 : ℝ) ≤ ((47616451657367724357/47630000000000000000 : ℝ)+(3485663599643/1428900000000000 : ℝ)*((10107/50000 : ℝ)+(237/4000 : ℝ)))^(131/32 : ℝ) := by
    rw [show (47616451657367724357/47630000000000000000 : ℝ)+(3485663599643/1428900000000000 : ℝ)*((10107/50000 : ℝ)+(237/4000 : ℝ))=(1250441482372229/1250000000000000 : ℝ) by norm_num, show 1+(71859459999349221/50000000000000000000 : ℝ)+(189113680831891/20000000000000000000 : ℝ)=(100144664488402857897/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71859459999349221/50000000000000000000 : ℝ) ≤ ((47616451657367724357/47630000000000000000 : ℝ)+2*(3485663599643/1428900000000000 : ℝ)*(10107/50000 : ℝ))^(131/32 : ℝ) := by
    rw [show (47616451657367724357/47630000000000000000 : ℝ)+2*(3485663599643/1428900000000000 : ℝ)*(10107/50000 : ℝ)=(400280700903099/400000000000000 : ℝ) by norm_num, show 1+2*(71859459999349221/50000000000000000000 : ℝ)=(25071859459999349221/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47616451657367724357/47630000000000000000 : ℝ)*(X 1 0+X 2 0)+(3485663599643/1428900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (237/4000 : ℝ)) (hi := (10107/50000 : ℝ)) (c := (47616451657367724357/47630000000000000000 : ℝ)) (alpha := (3485663599643/1428900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47616451657367724357/47630000000000000000 : ℝ)*(X 0 1+X 2 1)+(3485663599643/1428900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (237/4000 : ℝ)) (hi := (10107/50000 : ℝ)) (c := (47616451657367724357/47630000000000000000 : ℝ)) (alpha := (3485663599643/1428900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47616451657367724357/47630000000000000000 : ℝ)*(X 0 2+X 1 2)+(3485663599643/1428900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (131/32 : ℝ)) (lo := (237/4000 : ℝ)) (hi := (10107/50000 : ℝ)) (c := (47616451657367724357/47630000000000000000 : ℝ)) (alpha := (3485663599643/1428900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1063861449/5000000000 : ℝ)*X 0 0+(220061793/400000000 : ℝ)*X 0 1+(5167151477/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537174277/1000000000 : ℝ)*X 1 0+(-460248597/2000000000 : ℝ)*X 1 1+(5167155579/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335734027/625000000 : ℝ)*X 2 0+(5167153247/10000000000 : ℝ)*X 2 1+(-575310957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869600591/2000000000 : ℝ)*X 0 0+(2012408697/5000000000 : ℝ)*X 0 1+(4696610769/10000000000 : ℝ)*X 0 2+(869600591/2000000000 : ℝ)*X 1 0+(2012408697/5000000000 : ℝ)*X 1 1+(4696610769/10000000000 : ℝ)*X 1 2+(869600591/2000000000 : ℝ)*X 2 0+(2012408697/5000000000 : ℝ)*X 2 1+(4696610769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4255623/20000000 : ℝ)*X 0 0+(1292344733/2500000000 : ℝ)*X 0 1+(2749648289/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660827513/1250000000 : ℝ)*X 1 0+(-61534387/312500000 : ℝ)*X 1 1+(5499296593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321655067/2500000000 : ℝ)*X 2 0+(1374824151/2500000000 : ℝ)*X 2 1+(-1969100143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348183161/10000000000 : ℝ)*X 0 0+(586517313/1250000000 : ℝ)*X 0 1+(100733303/250000000 : ℝ)*X 0 2+(4348183161/10000000000 : ℝ)*X 1 0+(586517313/1250000000 : ℝ)*X 1 1+(100733303/250000000 : ℝ)*X 1 2+(4348183161/10000000000 : ℝ)*X 2 0+(586517313/1250000000 : ℝ)*X 2 1+(100733303/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1192_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (700953462890046381496019133/297687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (745305963/100000000000000 : ℝ)*(base23) + (143861447/100000000000000 : ℝ)*(upper2) + (37327/10000000000 : ℝ)*(upper3) + (22731859/10000000000000 : ℝ)*(upper4) + (279944639914659/12500000000000 : ℝ)*(major0) + (279944639914659/12500000000000 : ℝ)*(major1) + (279944639914659/12500000000000 : ℝ)*(major2) + (93453690043291/3125000000000 : ℝ)*(sp0) + (2990543776512363/100000000000000 : ℝ)*(sp1) + (747635369782609/25000000000000 : ℝ)*(sp2) + (744279510615061/50000000000000 : ℝ)*(sp3) + (25695127051/100000000000000 : ℝ)*(sp4) + (388018991/25000000000000 : ℝ)*(sp6) + (11362403313/100000000000000 : ℝ)*(sp7) + (372142595908359/25000000000000 : ℝ)*(f.failure) + (2990543776512363/100000000000000 : ℝ)*(f.sum) + (33915795708627/23815000000000000000000000000 : ℝ)*base65 + (5985895235976549263/595375000000000000000000000000000 : ℝ)*base67 + (8730675837968549263/595375000000000000000000000000000 : ℝ)*base69 + (4068321759183674263/595375000000000000000000000000000 : ℝ)*base71 + (110094740503657/23815000000000000000000000000 : ℝ)*base73 + (7723607435140424263/595375000000000000000000000000000 : ℝ)*base75 + (3602794954305924263/595375000000000000000000000000000 : ℝ)*base77 + (6865947591950549263/595375000000000000000000000000000 : ℝ)*base79 + (46959757516731/11907500000000000000000000000 : ℝ)*base81 + (33891/12500000000000000000 : ℝ)*base90 + (33891/12500000000000000000 : ℝ)*base92 + (33891/12500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6245154934215190698136201743/1190750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42032687/3125000000000 : ℝ)*(base19) + (1544538129/100000000000000 : ℝ)*(base23) + (23352659/100000000000000 : ℝ)*(upper2) + (87799773/50000000000000 : ℝ)*(upper3) + (22056003/20000000000000 : ℝ)*(upper5) + (1134948913472433/50000000000000 : ℝ)*(major0) + (1134948913472433/50000000000000 : ℝ)*(major1) + (1134948913472433/50000000000000 : ℝ)*(major2) + (13076143189/100000000000000 : ℝ)*(sp1) + (4220586013/25000000000000 : ℝ)*(sp2) + (47360288808401/1562500000000 : ℝ)*(sp4) + (757761015637123/25000000000000 : ℝ)*(sp5) + (757760014213871/25000000000000 : ℝ)*(sp6) + (1508736995327933/100000000000000 : ℝ)*(sp7) + (1508736995327933/100000000000000 : ℝ)*(f.failure) + (47360288808401/1562500000000 : ℝ)*(f.sum) + (12288130311649/23815000000000000000000000000 : ℝ)*base66 + (10418030877089450581/2381500000000000000000000000000000 : ℝ)*base67 + (5444280815721450581/2381500000000000000000000000000000 : ℝ)*base69 + (13338826779437049419/2381500000000000000000000000000000 : ℝ)*base72 + (157340591370661/23815000000000000000000000000 : ℝ)*base73 + (12445964887471049419/2381500000000000000000000000000000 : ℝ)*base76 + (9107119134294049419/2381500000000000000000000000000000 : ℝ)*base78 + (14460114380568549419/2381500000000000000000000000000000 : ℝ)*base80 + (25331476375483/11907500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (72817/50000000000000000000 : ℝ)*base90 + (72817/50000000000000000000 : ℝ)*base92 + (72817/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1192_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10107/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (237/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1192_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1192_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1192_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1192_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1192_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (8385/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (752251/500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1192_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
