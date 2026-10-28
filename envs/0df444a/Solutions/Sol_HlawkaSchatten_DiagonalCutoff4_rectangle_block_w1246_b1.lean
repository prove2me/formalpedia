-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1246_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:21:34.519576+00:00
-- url     : https://prove2.me/submissions/50ea62c7-c51d-4eab-84f0-219d029705dd

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
theorem support_rectangle_w1246_s3_0 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2115309643/10000000000 : ℝ)*x 0 + (5419316989/10000000000 : ℝ)*x 1 + (5240917917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115309643/10000000000 : ℝ)^8439 ≤ (12858479112193/100000000000000 : ℝ)^6391 := by
    have hnat : (2115309643 : ℕ)^8439*100000000000000^6391 ≤ 12858479112193^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115309643 10000000000 12858479112193 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419316989/10000000000 : ℝ)^8439 ≤ (4453350921589/10000000000000 : ℝ)^6391 := by
    have hnat : (5419316989 : ℕ)^8439*10000000000000^6391 ≤ 4453350921589^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419316989 10000000000 4453350921589 10000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240917917/10000000000 : ℝ)^8439 ≤ (42608011652819/100000000000000 : ℝ)^6391 := by
    have hnat : (5240917917 : ℕ)^8439*100000000000000^6391 ≤ 42608011652819^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240917917 10000000000 42608011652819 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2115309643/10000000000 : ℝ), (5419316989/10000000000 : ℝ), (5240917917/10000000000 : ℝ)] ![(12858479112193/100000000000000 : ℝ), (4453350921589/10000000000000 : ℝ), (42608011652819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2115309643/10000000000 : ℝ)|^8439 ≤ (12858479112193/100000000000000 : ℝ)^6391
        have hw : |(-2115309643/10000000000 : ℝ)|=(2115309643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419316989/10000000000 : ℝ)|^8439 ≤ (4453350921589/10000000000000 : ℝ)^6391
        have hw : |(5419316989/10000000000 : ℝ)|=(5419316989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240917917/10000000000 : ℝ)|^8439 ≤ (42608011652819/100000000000000 : ℝ)^6391
        have hw : |(5240917917/10000000000 : ℝ)|=(5240917917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_1 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351403761/10000000000 : ℝ)*x 0 + (-1103155737/5000000000 : ℝ)*x 1 + (524091803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351403761/10000000000 : ℝ)^8439 ≤ (21899037764493/50000000000000 : ℝ)^6391 := by
    have hnat : (5351403761 : ℕ)^8439*50000000000000^6391 ≤ 21899037764493^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351403761 10000000000 21899037764493 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103155737/5000000000 : ℝ)^8439 ≤ (3398477898663/25000000000000 : ℝ)^6391 := by
    have hnat : (1103155737 : ℕ)^8439*25000000000000^6391 ≤ 3398477898663^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103155737 5000000000 3398477898663 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524091803/1000000000 : ℝ)^8439 ≤ (8521602573177/20000000000000 : ℝ)^6391 := by
    have hnat : (524091803 : ℕ)^8439*20000000000000^6391 ≤ 8521602573177^6391*1000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524091803 1000000000 8521602573177 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351403761/10000000000 : ℝ), (-1103155737/5000000000 : ℝ), (524091803/1000000000 : ℝ)] ![(21899037764493/50000000000000 : ℝ), (3398477898663/25000000000000 : ℝ), (8521602573177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351403761/10000000000 : ℝ)|^8439 ≤ (21899037764493/50000000000000 : ℝ)^6391
        have hw : |(5351403761/10000000000 : ℝ)|=(5351403761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103155737/5000000000 : ℝ)|^8439 ≤ (3398477898663/25000000000000 : ℝ)^6391
        have hw : |(-1103155737/5000000000 : ℝ)|=(1103155737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524091803/1000000000 : ℝ)|^8439 ≤ (8521602573177/20000000000000 : ℝ)^6391
        have hw : |(524091803/1000000000 : ℝ)|=(524091803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_2 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070280739/2000000000 : ℝ)*x 0 + (5240918477/10000000000 : ℝ)*x 1 + (-551577743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070280739/2000000000 : ℝ)^8439 ≤ (43798074815717/100000000000000 : ℝ)^6391 := by
    have hnat : (1070280739 : ℕ)^8439*100000000000000^6391 ≤ 43798074815717^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070280739 2000000000 43798074815717 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240918477/10000000000 : ℝ)^8439 ≤ (1704320706579/4000000000000 : ℝ)^6391 := by
    have hnat : (5240918477 : ℕ)^8439*4000000000000^6391 ≤ 1704320706579^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240918477 10000000000 1704320706579 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551577743/2500000000 : ℝ)^8439 ≤ (2718781502097/20000000000000 : ℝ)^6391 := by
    have hnat : (551577743 : ℕ)^8439*20000000000000^6391 ≤ 2718781502097^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551577743 2500000000 2718781502097 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070280739/2000000000 : ℝ), (5240918477/10000000000 : ℝ), (-551577743/2500000000 : ℝ)] ![(43798074815717/100000000000000 : ℝ), (1704320706579/4000000000000 : ℝ), (2718781502097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070280739/2000000000 : ℝ)|^8439 ≤ (43798074815717/100000000000000 : ℝ)^6391
        have hw : |(1070280739/2000000000 : ℝ)|=(1070280739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240918477/10000000000 : ℝ)|^8439 ≤ (1704320706579/4000000000000 : ℝ)^6391
        have hw : |(5240918477/10000000000 : ℝ)|=(5240918477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-551577743/2500000000 : ℝ)|^8439 ≤ (2718781502097/20000000000000 : ℝ)^6391
        have hw : |(-551577743/2500000000 : ℝ)|=(551577743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_3 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348544953/10000000000 : ℝ)*x 0 + (2085558607/5000000000 : ℝ)*x 1 + (2266645171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348544953/10000000000 : ℝ)^8439 ≤ (33300523280181/100000000000000 : ℝ)^6391 := by
    have hnat : (4348544953 : ℕ)^8439*100000000000000^6391 ≤ 33300523280181^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348544953 10000000000 33300523280181 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085558607/5000000000 : ℝ)^8439 ≤ (6303649091207/20000000000000 : ℝ)^6391 := by
    have hnat : (2085558607 : ℕ)^8439*20000000000000^6391 ≤ 6303649091207^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085558607 5000000000 6303649091207 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266645171/5000000000 : ℝ)^8439 ≤ (35181231256499/100000000000000 : ℝ)^6391 := by
    have hnat : (2266645171 : ℕ)^8439*100000000000000^6391 ≤ 35181231256499^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266645171 5000000000 35181231256499 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348544953/10000000000 : ℝ), (2085558607/5000000000 : ℝ), (2266645171/5000000000 : ℝ)] ![(33300523280181/100000000000000 : ℝ), (6303649091207/20000000000000 : ℝ), (35181231256499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348544953/10000000000 : ℝ)|^8439 ≤ (33300523280181/100000000000000 : ℝ)^6391
        have hw : |(4348544953/10000000000 : ℝ)|=(4348544953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085558607/5000000000 : ℝ)|^8439 ≤ (6303649091207/20000000000000 : ℝ)^6391
        have hw : |(2085558607/5000000000 : ℝ)|=(2085558607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2266645171/5000000000 : ℝ)|^8439 ≤ (35181231256499/100000000000000 : ℝ)^6391
        have hw : |(2266645171/5000000000 : ℝ)|=(2266645171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_4 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057661911/5000000000 : ℝ)*x 0 + (1310391243/2500000000 : ℝ)*x 1 + (216746653/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057661911/5000000000 : ℝ)^8439 ≤ (6429296461551/50000000000000 : ℝ)^6391 := by
    have hnat : (1057661911 : ℕ)^8439*50000000000000^6391 ≤ 6429296461551^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057661911 5000000000 6429296461551 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310391243/2500000000 : ℝ)^8439 ≤ (21307478995057/50000000000000 : ℝ)^6391 := by
    have hnat : (1310391243 : ℕ)^8439*50000000000000^6391 ≤ 21307478995057^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310391243 2500000000 21307478995057 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216746653/400000000 : ℝ)^8439 ≤ (44526449081677/100000000000000 : ℝ)^6391 := by
    have hnat : (216746653 : ℕ)^8439*100000000000000^6391 ≤ 44526449081677^6391*400000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216746653 400000000 44526449081677 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057661911/5000000000 : ℝ), (1310391243/2500000000 : ℝ), (216746653/400000000 : ℝ)] ![(6429296461551/50000000000000 : ℝ), (21307478995057/50000000000000 : ℝ), (44526449081677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057661911/5000000000 : ℝ)|^8439 ≤ (6429296461551/50000000000000 : ℝ)^6391
        have hw : |(-1057661911/5000000000 : ℝ)|=(1057661911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310391243/2500000000 : ℝ)|^8439 ≤ (21307478995057/50000000000000 : ℝ)^6391
        have hw : |(1310391243/2500000000 : ℝ)|=(1310391243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216746653/400000000 : ℝ)|^8439 ≤ (44526449081677/100000000000000 : ℝ)^6391
        have hw : |(216746653/400000000 : ℝ)|=(216746653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_5 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652938773/5000000000 : ℝ)*x 0 + (-405712621/2000000000 : ℝ)*x 1 + (1083733309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652938773/5000000000 : ℝ)^8439 ≤ (866134815383/2000000000000 : ℝ)^6391 := by
    have hnat : (2652938773 : ℕ)^8439*2000000000000^6391 ≤ 866134815383^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652938773 5000000000 866134815383 2000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405712621/2000000000 : ℝ)^8439 ≤ (3041701934717/25000000000000 : ℝ)^6391 := by
    have hnat : (405712621 : ℕ)^8439*25000000000000^6391 ≤ 3041701934717^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405712621 2000000000 3041701934717 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083733309/2000000000 : ℝ)^8439 ≤ (44526451468777/100000000000000 : ℝ)^6391 := by
    have hnat : (1083733309 : ℕ)^8439*100000000000000^6391 ≤ 44526451468777^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083733309 2000000000 44526451468777 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652938773/5000000000 : ℝ), (-405712621/2000000000 : ℝ), (1083733309/2000000000 : ℝ)] ![(866134815383/2000000000000 : ℝ), (3041701934717/25000000000000 : ℝ), (44526451468777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652938773/5000000000 : ℝ)|^8439 ≤ (866134815383/2000000000000 : ℝ)^6391
        have hw : |(2652938773/5000000000 : ℝ)|=(2652938773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405712621/2000000000 : ℝ)|^8439 ≤ (3041701934717/25000000000000 : ℝ)^6391
        have hw : |(-405712621/2000000000 : ℝ)|=(405712621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083733309/2000000000 : ℝ)|^8439 ≤ (44526451468777/100000000000000 : ℝ)^6391
        have hw : |(1083733309/2000000000 : ℝ)|=(1083733309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_6 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305877639/10000000000 : ℝ)*x 0 + (2709333227/5000000000 : ℝ)*x 1 + (-63392597/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305877639/10000000000 : ℝ)^8439 ≤ (43306741771463/100000000000000 : ℝ)^6391 := by
    have hnat : (5305877639 : ℕ)^8439*100000000000000^6391 ≤ 43306741771463^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305877639 10000000000 43306741771463 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709333227/5000000000 : ℝ)^8439 ≤ (8905290096277/20000000000000 : ℝ)^6391 := by
    have hnat : (2709333227 : ℕ)^8439*20000000000000^6391 ≤ 8905290096277^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709333227 5000000000 8905290096277 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63392597/312500000 : ℝ)^8439 ≤ (12166807730949/100000000000000 : ℝ)^6391 := by
    have hnat : (63392597 : ℕ)^8439*100000000000000^6391 ≤ 12166807730949^6391*312500000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63392597 312500000 12166807730949 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305877639/10000000000 : ℝ), (2709333227/5000000000 : ℝ), (-63392597/312500000 : ℝ)] ![(43306741771463/100000000000000 : ℝ), (8905290096277/20000000000000 : ℝ), (12166807730949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305877639/10000000000 : ℝ)|^8439 ≤ (43306741771463/100000000000000 : ℝ)^6391
        have hw : |(5305877639/10000000000 : ℝ)|=(5305877639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709333227/5000000000 : ℝ)|^8439 ≤ (8905290096277/20000000000000 : ℝ)^6391
        have hw : |(2709333227/5000000000 : ℝ)|=(2709333227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63392597/312500000 : ℝ)|^8439 ≤ (12166807730949/100000000000000 : ℝ)^6391
        have hw : |(-63392597/312500000 : ℝ)|=(63392597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s3_7 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4348573289/10000000000 : ℝ)*x 0 + (4531977417/10000000000 : ℝ)*x 1 + (2086218397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348573289/10000000000 : ℝ)^8439 ≤ (4162601226121/12500000000000 : ℝ)^6391 := by
    have hnat : (4348573289 : ℕ)^8439*12500000000000^6391 ≤ 4162601226121^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348573289 10000000000 4162601226121 12500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531977417/10000000000 : ℝ)^8439 ≤ (35167777627973/100000000000000 : ℝ)^6391 := by
    have hnat : (4531977417 : ℕ)^8439*100000000000000^6391 ≤ 35167777627973^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531977417 10000000000 35167777627973 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086218397/5000000000 : ℝ)^8439 ≤ (31531412538177/100000000000000 : ℝ)^6391 := by
    have hnat : (2086218397 : ℕ)^8439*100000000000000^6391 ≤ 31531412538177^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086218397 5000000000 31531412538177 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348573289/10000000000 : ℝ), (4531977417/10000000000 : ℝ), (2086218397/5000000000 : ℝ)] ![(4162601226121/12500000000000 : ℝ), (35167777627973/100000000000000 : ℝ), (31531412538177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348573289/10000000000 : ℝ)|^8439 ≤ (4162601226121/12500000000000 : ℝ)^6391
        have hw : |(4348573289/10000000000 : ℝ)|=(4348573289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531977417/10000000000 : ℝ)|^8439 ≤ (35167777627973/100000000000000 : ℝ)^6391
        have hw : |(4531977417/10000000000 : ℝ)|=(4531977417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086218397/5000000000 : ℝ)|^8439 ≤ (31531412538177/100000000000000 : ℝ)^6391
        have hw : |(2086218397/5000000000 : ℝ)|=(2086218397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1246_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10921/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14697/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16213/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1903/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16213/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1903/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16213/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1903/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16213/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1903/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16213/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1903/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16213/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1903/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1903/20000 : ℝ) ^ (4219/1024 : ℝ) ≤ (247163592611917/4000000000000000000 : ℝ) := by
    have hpowers : (1903/20000 : ℝ)^4219 ≤ (247163592611917/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1903 : ℕ)^4219*4000000000000000000^1024 ≤ 247163592611917^1024*20000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1903 20000 247163592611917 4000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1903/20000 : ℝ)) (X := (247163592611917/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16213/100000 : ℝ) ^ (4219/1024 : ℝ) ≤ (11106431394194669/20000000000000000000 : ℝ) := by
    have hpowers : (16213/100000 : ℝ)^4219 ≤ (11106431394194669/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16213 : ℕ)^4219*20000000000000000000^1024 ≤ 11106431394194669^1024*100000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16213 100000 11106431394194669 20000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16213/100000 : ℝ)) (X := (11106431394194669/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000247163592611917/2000000000000000000 : ℝ) ≤ (10000299933250129/10000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (2000247163592611917/2000000000000000000 : ℝ)^1024 ≤ (10000299933250129/10000000000000000 : ℝ)^4219 := by
      have hnat : (2000247163592611917 : ℕ)^1024*10000000000000000^4219 ≤ 10000299933250129^4219*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000247163592611917 2000000000000000000 10000299933250129 10000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000299933250129/10000000000000000 : ℝ)) (X := (2000247163592611917/2000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006171124678627127/10000000000000000000 : ℝ) ≤ (625093590833349/625000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (10006171124678627127/10000000000000000000 : ℝ)^1024 ≤ (625093590833349/625000000000000 : ℝ)^4219 := by
      have hnat : (10006171124678627127 : ℕ)^1024*625000000000000^4219 ≤ 625093590833349^4219*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006171124678627127 10000000000000000000 625093590833349 625000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625093590833349/625000000000000 : ℝ)) (X := (10006171124678627127/10000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10011106431394194669/10000000000000000000 : ℝ) ≤ (10002694973417039/10000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (10011106431394194669/10000000000000000000 : ℝ)^1024 ≤ (10002694973417039/10000000000000000 : ℝ)^4219 := by
      have hnat : (10011106431394194669 : ℕ)^1024*10000000000000000^4219 ≤ 10002694973417039^4219*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011106431394194669 10000000000000000000 10002694973417039 10000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002694973417039/10000000000000000 : ℝ)) (X := (10011106431394194669/10000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(247163592611917/4000000000000000000 : ℝ) ≤ ((2092475629553787981/2093125000000000000 : ℝ)+2*(239504016691/133960000000000 : ℝ)*(1903/20000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (2092475629553787981/2093125000000000000 : ℝ)+2*(239504016691/133960000000000 : ℝ)*(1903/20000 : ℝ)=(10000299933250129/10000000000000000 : ℝ) by norm_num, show 1+2*(247163592611917/4000000000000000000 : ℝ)=(2000247163592611917/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11106431394194669/20000000000000000000 : ℝ)+(247163592611917/4000000000000000000 : ℝ) ≤ ((2092475629553787981/2093125000000000000 : ℝ)+(239504016691/133960000000000 : ℝ)*((16213/100000 : ℝ)+(1903/20000 : ℝ)))^(4219/1024 : ℝ) := by
    rw [show (2092475629553787981/2093125000000000000 : ℝ)+(239504016691/133960000000000 : ℝ)*((16213/100000 : ℝ)+(1903/20000 : ℝ))=(625093590833349/625000000000000 : ℝ) by norm_num, show 1+(11106431394194669/20000000000000000000 : ℝ)+(247163592611917/4000000000000000000 : ℝ)=(10006171124678627127/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11106431394194669/20000000000000000000 : ℝ) ≤ ((2092475629553787981/2093125000000000000 : ℝ)+2*(239504016691/133960000000000 : ℝ)*(16213/100000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (2092475629553787981/2093125000000000000 : ℝ)+2*(239504016691/133960000000000 : ℝ)*(16213/100000 : ℝ)=(10002694973417039/10000000000000000 : ℝ) by norm_num, show 1+2*(11106431394194669/20000000000000000000 : ℝ)=(10011106431394194669/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2092475629553787981/2093125000000000000 : ℝ)*(X 1 0+X 2 0)+(239504016691/133960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (1903/20000 : ℝ)) (hi := (16213/100000 : ℝ)) (c := (2092475629553787981/2093125000000000000 : ℝ)) (alpha := (239504016691/133960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2092475629553787981/2093125000000000000 : ℝ)*(X 0 1+X 2 1)+(239504016691/133960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (1903/20000 : ℝ)) (hi := (16213/100000 : ℝ)) (c := (2092475629553787981/2093125000000000000 : ℝ)) (alpha := (239504016691/133960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2092475629553787981/2093125000000000000 : ℝ)*(X 0 2+X 1 2)+(239504016691/133960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (1903/20000 : ℝ)) (hi := (16213/100000 : ℝ)) (c := (2092475629553787981/2093125000000000000 : ℝ)) (alpha := (239504016691/133960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2115309643/10000000000 : ℝ)*X 0 0+(5419316989/10000000000 : ℝ)*X 0 1+(5240917917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351403761/10000000000 : ℝ)*X 1 0+(-1103155737/5000000000 : ℝ)*X 1 1+(524091803/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070280739/2000000000 : ℝ)*X 2 0+(5240918477/10000000000 : ℝ)*X 2 1+(-551577743/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348544953/10000000000 : ℝ)*X 0 0+(2085558607/5000000000 : ℝ)*X 0 1+(2266645171/5000000000 : ℝ)*X 0 2+(4348544953/10000000000 : ℝ)*X 1 0+(2085558607/5000000000 : ℝ)*X 1 1+(2266645171/5000000000 : ℝ)*X 1 2+(4348544953/10000000000 : ℝ)*X 2 0+(2085558607/5000000000 : ℝ)*X 2 1+(2266645171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1057661911/5000000000 : ℝ)*X 0 0+(1310391243/2500000000 : ℝ)*X 0 1+(216746653/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652938773/5000000000 : ℝ)*X 1 0+(-405712621/2000000000 : ℝ)*X 1 1+(1083733309/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305877639/10000000000 : ℝ)*X 2 0+(2709333227/5000000000 : ℝ)*X 2 1+(-63392597/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348573289/10000000000 : ℝ)*X 0 0+(4531977417/10000000000 : ℝ)*X 0 1+(2086218397/5000000000 : ℝ)*X 0 2+(4348573289/10000000000 : ℝ)*X 1 0+(4531977417/10000000000 : ℝ)*X 1 1+(2086218397/5000000000 : ℝ)*X 1 2+(4348573289/10000000000 : ℝ)*X 2 0+(4531977417/10000000000 : ℝ)*X 2 1+(2086218397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29668562696478124711869/3349000000000000000000000000 : ℝ) := by norm_num
    linear_combination (632064409/50000000000000 : ℝ)*(base19) + (824930429/100000000000000 : ℝ)*(base23) + (108358957/50000000000000 : ℝ)*(lower2) + (120289393/100000000000000 : ℝ)*(upper5) + (261456890918283/6250000000000 : ℝ)*(major0) + (261456890918283/6250000000000 : ℝ)*(major1) + (261456890918283/6250000000000 : ℝ)*(major2) + (5605443032950861/100000000000000 : ℝ)*(sp0) + (5605479178512171/100000000000000 : ℝ)*(sp1) + (2802741860564989/50000000000000 : ℝ)*(sp2) + (2761123122338249/100000000000000 : ℝ)*(sp3) + (20756554773/50000000000000 : ℝ)*(sp4) + (2051709709/50000000000000 : ℝ)*(sp5) + (12545688667/100000000000000 : ℝ)*(sp7) + (690283917006729/25000000000000 : ℝ)*(f.failure) + (5605484546060407/100000000000000 : ℝ)*(f.sum) + (11809356185701/3349000000000000000000000000 : ℝ)*base66 + (57117706699308629/26164062500000000000000000000000 : ℝ)*base68 + (207644678865382883/52328125000000000000000000000000 : ℝ)*base70 + (317993080542054617/52328125000000000000000000000000 : ℝ)*base71 + (3945186578089/669800000000000000000000000 : ℝ)*base74 + (11677501287145499/6541015625000000000000000000000 : ℝ)*base75 + (164642604954628871/26164062500000000000000000000000 : ℝ)*base77 + (851376648312445383/52328125000000000000000000000000 : ℝ)*base80 + (861575522609/837250000000000000000000000 : ℝ)*base82 + (3265041/2500000000000000000000 : ℝ)*base90 + (3265041/2500000000000000000000 : ℝ)*base92 + (3265041/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250458189323657685274429287/52328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406683441/100000000000000 : ℝ)*(base19) + (170597173/25000000000000 : ℝ)*(base23) + (78099643/50000000000000 : ℝ)*(upper3) + (32091621/50000000000000 : ℝ)*(lower4) + (29989969/100000000000000 : ℝ)*(upper5) + (2106952081059047/50000000000000 : ℝ)*(major0) + (2106952081059047/50000000000000 : ℝ)*(major1) + (2106952081059047/50000000000000 : ℝ)*(major2) + (1736594049/20000000000000 : ℝ)*(sp1) + (3036529789/20000000000000 : ℝ)*(sp2) + (5646479414184773/100000000000000 : ℝ)*(sp4) + (2823235162265543/50000000000000 : ℝ)*(sp5) + (2757062279857/48828125000 : ℝ)*(sp6) + (2781328750508017/100000000000000 : ℝ)*(sp7) + (2781328750508017/100000000000000 : ℝ)*(f.failure) + (5646479414184773/100000000000000 : ℝ)*(f.sum) + (4948014800267/1674500000000000000000000000 : ℝ)*base65 + (322443187356105491/52328125000000000000000000000000 : ℝ)*base67 + (473842933324511741/52328125000000000000000000000000 : ℝ)*base69 + (113738507035232433/26164062500000000000000000000000 : ℝ)*base71 + (153464645629/52328125000000000000000000 : ℝ)*base73 + (427608660277451183/26164062500000000000000000000000 : ℝ)*base75 + (22154026080030279/13082031250000000000000000000000 : ℝ)*base77 + (273312070229638683/26164062500000000000000000000000 : ℝ)*base79 + (5481420309391/3349000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (83915193/10000000000000000000000 : ℝ)*base90 + (83915193/10000000000000000000000 : ℝ)*base92 + (83915193/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1246_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10921/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1246_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1246_s4_0 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132348673/625000000 : ℝ)*x 0 + (5397334413/10000000000 : ℝ)*x 1 + (5261413339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132348673/625000000 : ℝ)^8439 ≤ (1287669586079/10000000000000 : ℝ)^6391 := by
    have hnat : (132348673 : ℕ)^8439*10000000000000^6391 ≤ 1287669586079^6391*625000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132348673 625000000 1287669586079 10000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397334413/10000000000 : ℝ)^8439 ≤ (44295134326363/100000000000000 : ℝ)^6391 := by
    have hnat : (5397334413 : ℕ)^8439*100000000000000^6391 ≤ 44295134326363^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397334413 10000000000 44295134326363 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261413339/10000000000 : ℝ)^8439 ≤ (42828169789699/100000000000000 : ℝ)^6391 := by
    have hnat : (5261413339 : ℕ)^8439*100000000000000^6391 ≤ 42828169789699^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261413339 10000000000 42828169789699 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132348673/625000000 : ℝ), (5397334413/10000000000 : ℝ), (5261413339/10000000000 : ℝ)] ![(1287669586079/10000000000000 : ℝ), (44295134326363/100000000000000 : ℝ), (42828169789699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132348673/625000000 : ℝ)|^8439 ≤ (1287669586079/10000000000000 : ℝ)^6391
        have hw : |(-132348673/625000000 : ℝ)|=(132348673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397334413/10000000000 : ℝ)|^8439 ≤ (44295134326363/100000000000000 : ℝ)^6391
        have hw : |(5397334413/10000000000 : ℝ)|=(5397334413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261413339/10000000000 : ℝ)|^8439 ≤ (42828169789699/100000000000000 : ℝ)^6391
        have hw : |(5261413339/10000000000 : ℝ)|=(5261413339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_1 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336464943/2500000000 : ℝ)*x 0 + (-273323243/1250000000 : ℝ)*x 1 + (5261413343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336464943/2500000000 : ℝ)^8439 ≤ (8747634198123/20000000000000 : ℝ)^6391 := by
    have hnat : (1336464943 : ℕ)^8439*20000000000000^6391 ≤ 8747634198123^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336464943 2500000000 8747634198123 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273323243/1250000000 : ℝ)^8439 ≤ (13433659161957/100000000000000 : ℝ)^6391 := by
    have hnat : (273323243 : ℕ)^8439*100000000000000^6391 ≤ 13433659161957^6391*1250000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273323243 1250000000 13433659161957 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261413343/10000000000 : ℝ)^8439 ≤ (42828169832693/100000000000000 : ℝ)^6391 := by
    have hnat : (5261413343 : ℕ)^8439*100000000000000^6391 ≤ 42828169832693^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261413343 10000000000 42828169832693 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336464943/2500000000 : ℝ), (-273323243/1250000000 : ℝ), (5261413343/10000000000 : ℝ)] ![(8747634198123/20000000000000 : ℝ), (13433659161957/100000000000000 : ℝ), (42828169832693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336464943/2500000000 : ℝ)|^8439 ≤ (8747634198123/20000000000000 : ℝ)^6391
        have hw : |(1336464943/2500000000 : ℝ)|=(1336464943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273323243/1250000000 : ℝ)|^8439 ≤ (13433659161957/100000000000000 : ℝ)^6391
        have hw : |(-273323243/1250000000 : ℝ)|=(273323243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261413343/10000000000 : ℝ)|^8439 ≤ (42828169832693/100000000000000 : ℝ)^6391
        have hw : |(5261413343/10000000000 : ℝ)|=(5261413343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_2 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (42766879/80000000 : ℝ)*x 0 + (2630706603/5000000000 : ℝ)*x 1 + (-2186585987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42766879/80000000 : ℝ)^8439 ≤ (43738172103377/100000000000000 : ℝ)^6391 := by
    have hnat : (42766879 : ℕ)^8439*100000000000000^6391 ≤ 43738172103377^6391*80000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42766879 80000000 43738172103377 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630706603/5000000000 : ℝ)^8439 ≤ (2676760522509/6250000000000 : ℝ)^6391 := by
    have hnat : (2630706603 : ℕ)^8439*6250000000000^6391 ≤ 2676760522509^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630706603 5000000000 2676760522509 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186585987/10000000000 : ℝ)^8439 ≤ (1343365951079/10000000000000 : ℝ)^6391 := by
    have hnat : (2186585987 : ℕ)^8439*10000000000000^6391 ≤ 1343365951079^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186585987 10000000000 1343365951079 10000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42766879/80000000 : ℝ), (2630706603/5000000000 : ℝ), (-2186585987/10000000000 : ℝ)] ![(43738172103377/100000000000000 : ℝ), (2676760522509/6250000000000 : ℝ), (1343365951079/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42766879/80000000 : ℝ)|^8439 ≤ (43738172103377/100000000000000 : ℝ)^6391
        have hw : |(42766879/80000000 : ℝ)|=(42766879/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630706603/5000000000 : ℝ)|^8439 ≤ (2676760522509/6250000000000 : ℝ)^6391
        have hw : |(2630706603/5000000000 : ℝ)|=(2630706603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186585987/10000000000 : ℝ)|^8439 ≤ (1343365951079/10000000000000 : ℝ)^6391
        have hw : |(-2186585987/10000000000 : ℝ)|=(2186585987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_3 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174952691/5000000000 : ℝ)*x 0 + (4214060959/10000000000 : ℝ)*x 1 + (4489999597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174952691/5000000000 : ℝ)^8439 ≤ (33314280380743/100000000000000 : ℝ)^6391 := by
    have hnat : (2174952691 : ℕ)^8439*100000000000000^6391 ≤ 33314280380743^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174952691 5000000000 33314280380743 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4214060959/10000000000 : ℝ)^8439 ≤ (31947431790051/100000000000000 : ℝ)^6391 := by
    have hnat : (4214060959 : ℕ)^8439*100000000000000^6391 ≤ 31947431790051^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214060959 10000000000 31947431790051 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4489999597/10000000000 : ℝ)^8439 ≤ (34738287819399/100000000000000 : ℝ)^6391 := by
    have hnat : (4489999597 : ℕ)^8439*100000000000000^6391 ≤ 34738287819399^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489999597 10000000000 34738287819399 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174952691/5000000000 : ℝ), (4214060959/10000000000 : ℝ), (4489999597/10000000000 : ℝ)] ![(33314280380743/100000000000000 : ℝ), (31947431790051/100000000000000 : ℝ), (34738287819399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174952691/5000000000 : ℝ)|^8439 ≤ (33314280380743/100000000000000 : ℝ)^6391
        have hw : |(2174952691/5000000000 : ℝ)|=(2174952691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4214060959/10000000000 : ℝ)|^8439 ≤ (31947431790051/100000000000000 : ℝ)^6391
        have hw : |(4214060959/10000000000 : ℝ)|=(4214060959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4489999597/10000000000 : ℝ)|^8439 ≤ (34738287819399/100000000000000 : ℝ)^6391
        have hw : |(4489999597/10000000000 : ℝ)|=(4489999597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_4 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117584891/10000000000 : ℝ)*x 0 + (1315447353/2500000000 : ℝ)*x 1 + (674619607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117584891/10000000000 : ℝ)^8439 ≤ (515069801011/4000000000000 : ℝ)^6391 := by
    have hnat : (2117584891 : ℕ)^8439*4000000000000^6391 ≤ 515069801011^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117584891 10000000000 515069801011 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315447353/2500000000 : ℝ)^8439 ≤ (42832212069689/100000000000000 : ℝ)^6391 := by
    have hnat : (1315447353 : ℕ)^8439*100000000000000^6391 ≤ 42832212069689^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315447353 2500000000 42832212069689 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674619607/1250000000 : ℝ)^8439 ≤ (44291042883187/100000000000000 : ℝ)^6391 := by
    have hnat : (674619607 : ℕ)^8439*100000000000000^6391 ≤ 44291042883187^6391*1250000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674619607 1250000000 44291042883187 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117584891/10000000000 : ℝ), (1315447353/2500000000 : ℝ), (674619607/1250000000 : ℝ)] ![(515069801011/4000000000000 : ℝ), (42832212069689/100000000000000 : ℝ), (44291042883187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117584891/10000000000 : ℝ)|^8439 ≤ (515069801011/4000000000000 : ℝ)^6391
        have hw : |(-2117584891/10000000000 : ℝ)|=(2117584891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315447353/2500000000 : ℝ)|^8439 ≤ (42832212069689/100000000000000 : ℝ)^6391
        have hw : |(1315447353/2500000000 : ℝ)|=(1315447353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674619607/1250000000 : ℝ)|^8439 ≤ (44291042883187/100000000000000 : ℝ)^6391
        have hw : |(674619607/1250000000 : ℝ)|=(674619607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_5 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265558571/500000000 : ℝ)*x 0 + (-2051042451/10000000000 : ℝ)*x 1 + (2698478373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265558571/500000000 : ℝ)^8439 ≤ (21681902466213/50000000000000 : ℝ)^6391 := by
    have hnat : (265558571 : ℕ)^8439*50000000000000^6391 ≤ 21681902466213^6391*500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265558571 500000000 21681902466213 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051042451/10000000000 : ℝ)^8439 ≤ (385786042583/3125000000000 : ℝ)^6391 := by
    have hnat : (2051042451 : ℕ)^8439*3125000000000^6391 ≤ 385786042583^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051042451 10000000000 385786042583 3125000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698478373/5000000000 : ℝ)^8439 ≤ (11072760422793/25000000000000 : ℝ)^6391 := by
    have hnat : (2698478373 : ℕ)^8439*25000000000000^6391 ≤ 11072760422793^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698478373 5000000000 11072760422793 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265558571/500000000 : ℝ), (-2051042451/10000000000 : ℝ), (2698478373/5000000000 : ℝ)] ![(21681902466213/50000000000000 : ℝ), (385786042583/3125000000000 : ℝ), (11072760422793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265558571/500000000 : ℝ)|^8439 ≤ (21681902466213/50000000000000 : ℝ)^6391
        have hw : |(265558571/500000000 : ℝ)|=(265558571/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051042451/10000000000 : ℝ)|^8439 ≤ (385786042583/3125000000000 : ℝ)^6391
        have hw : |(-2051042451/10000000000 : ℝ)|=(2051042451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698478373/5000000000 : ℝ)|^8439 ≤ (11072760422793/25000000000000 : ℝ)^6391
        have hw : |(2698478373/5000000000 : ℝ)|=(2698478373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_6 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311171013/10000000000 : ℝ)*x 0 + (2698478647/5000000000 : ℝ)*x 1 + (-410208451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311171013/10000000000 : ℝ)^8439 ≤ (43363800544557/100000000000000 : ℝ)^6391 := by
    have hnat : (5311171013 : ℕ)^8439*100000000000000^6391 ≤ 43363800544557^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311171013 10000000000 43363800544557 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698478647/5000000000 : ℝ)^8439 ≤ (1771641905183/4000000000000 : ℝ)^6391 := by
    have hnat : (2698478647 : ℕ)^8439*4000000000000^6391 ≤ 1771641905183^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698478647 5000000000 1771641905183 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410208451/2000000000 : ℝ)^8439 ≤ (6172575902449/50000000000000 : ℝ)^6391 := by
    have hnat : (410208451 : ℕ)^8439*50000000000000^6391 ≤ 6172575902449^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410208451 2000000000 6172575902449 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311171013/10000000000 : ℝ), (2698478647/5000000000 : ℝ), (-410208451/2000000000 : ℝ)] ![(43363800544557/100000000000000 : ℝ), (1771641905183/4000000000000 : ℝ), (6172575902449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311171013/10000000000 : ℝ)|^8439 ≤ (43363800544557/100000000000000 : ℝ)^6391
        have hw : |(5311171013/10000000000 : ℝ)|=(5311171013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698478647/5000000000 : ℝ)|^8439 ≤ (1771641905183/4000000000000 : ℝ)^6391
        have hw : |(2698478647/5000000000 : ℝ)|=(2698478647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410208451/2000000000 : ℝ)|^8439 ≤ (6172575902449/50000000000000 : ℝ)^6391
        have hw : |(-410208451/2000000000 : ℝ)|=(410208451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s4_7 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349918017/10000000000 : ℝ)*x 0 + (4489236417/10000000000 : ℝ)*x 1 + (2107413501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349918017/10000000000 : ℝ)^8439 ≤ (6662881631287/20000000000000 : ℝ)^6391 := by
    have hnat : (4349918017 : ℕ)^8439*20000000000000^6391 ≤ 6662881631287^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349918017 10000000000 6662881631287 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489236417/10000000000 : ℝ)^8439 ≤ (6946098264793/20000000000000 : ℝ)^6391 := by
    have hnat : (4489236417 : ℕ)^8439*20000000000000^6391 ≤ 6946098264793^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489236417 10000000000 6946098264793 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107413501/5000000000 : ℝ)^8439 ≤ (31955100513991/100000000000000 : ℝ)^6391 := by
    have hnat : (2107413501 : ℕ)^8439*100000000000000^6391 ≤ 31955100513991^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107413501 5000000000 31955100513991 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349918017/10000000000 : ℝ), (4489236417/10000000000 : ℝ), (2107413501/5000000000 : ℝ)] ![(6662881631287/20000000000000 : ℝ), (6946098264793/20000000000000 : ℝ), (31955100513991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349918017/10000000000 : ℝ)|^8439 ≤ (6662881631287/20000000000000 : ℝ)^6391
        have hw : |(4349918017/10000000000 : ℝ)|=(4349918017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489236417/10000000000 : ℝ)|^8439 ≤ (6946098264793/20000000000000 : ℝ)^6391
        have hw : |(4489236417/10000000000 : ℝ)|=(4489236417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107413501/5000000000 : ℝ)|^8439 ≤ (31955100513991/100000000000000 : ℝ)^6391
        have hw : |(2107413501/5000000000 : ℝ)|=(2107413501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1246_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5679/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10921/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10921/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10921/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10921/100000 : ℝ) ^ (4219/1024 : ℝ) ≤ (10902558198657679/100000000000000000000 : ℝ) := by
    have hpowers : (10921/100000 : ℝ)^4219 ≤ (10902558198657679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10921 : ℕ)^4219*100000000000000000000^1024 ≤ 10902558198657679^1024*100000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10921 100000 10902558198657679 100000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10921/100000 : ℝ)) (X := (10902558198657679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14697/100000 : ℝ) ^ (4219/1024 : ℝ) ≤ (231613914676089/625000000000000000 : ℝ) := by
    have hpowers : (14697/100000 : ℝ)^4219 ≤ (231613914676089/625000000000000000 : ℝ)^1024 := by
      have hnat : (14697 : ℕ)^4219*625000000000000000^1024 ≤ 231613914676089^1024*100000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14697 100000 231613914676089 625000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14697/100000 : ℝ)) (X := (231613914676089/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010902558198657679/50000000000000000000 : ℝ) ≤ (10000529191654543/10000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (50010902558198657679/50000000000000000000 : ℝ)^1024 ≤ (10000529191654543/10000000000000000 : ℝ)^4219 := by
      have hnat : (50010902558198657679 : ℕ)^1024*10000000000000000^4219 ≤ 10000529191654543^4219*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010902558198657679 50000000000000000000 10000529191654543 10000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000529191654543/10000000000000000 : ℝ)) (X := (50010902558198657679/50000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047960784546831919/100000000000000000000 : ℝ) ≤ (5000581926133367/5000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (100047960784546831919/100000000000000000000 : ℝ)^1024 ≤ (5000581926133367/5000000000000000 : ℝ)^4219 := by
      have hnat : (100047960784546831919 : ℕ)^1024*5000000000000000^4219 ≤ 5000581926133367^4219*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047960784546831919 100000000000000000000 5000581926133367 5000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000581926133367/5000000000000000 : ℝ)) (X := (100047960784546831919/100000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312731613914676089/312500000000000000 : ℝ) ≤ (400071940515157/400000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (312731613914676089/312500000000000000 : ℝ)^1024 ≤ (400071940515157/400000000000000 : ℝ)^4219 := by
      have hnat : (312731613914676089 : ℕ)^1024*400000000000000^4219 ≤ 400071940515157^4219*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312731613914676089 312500000000000000 400071940515157 400000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400071940515157/400000000000000 : ℝ)) (X := (312731613914676089/312500000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10902558198657679/100000000000000000000 : ℝ) ≤ ((18874067985298039273/18880000000000000000 : ℝ)+2*(634660612191/377600000000000 : ℝ)*(10921/100000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (18874067985298039273/18880000000000000000 : ℝ)+2*(634660612191/377600000000000 : ℝ)*(10921/100000 : ℝ)=(10000529191654543/10000000000000000 : ℝ) by norm_num, show 1+2*(10902558198657679/100000000000000000000 : ℝ)=(50010902558198657679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(231613914676089/625000000000000000 : ℝ)+(10902558198657679/100000000000000000000 : ℝ) ≤ ((18874067985298039273/18880000000000000000 : ℝ)+(634660612191/377600000000000 : ℝ)*((14697/100000 : ℝ)+(10921/100000 : ℝ)))^(4219/1024 : ℝ) := by
    rw [show (18874067985298039273/18880000000000000000 : ℝ)+(634660612191/377600000000000 : ℝ)*((14697/100000 : ℝ)+(10921/100000 : ℝ))=(5000581926133367/5000000000000000 : ℝ) by norm_num, show 1+(231613914676089/625000000000000000 : ℝ)+(10902558198657679/100000000000000000000 : ℝ)=(100047960784546831919/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(231613914676089/625000000000000000 : ℝ) ≤ ((18874067985298039273/18880000000000000000 : ℝ)+2*(634660612191/377600000000000 : ℝ)*(14697/100000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (18874067985298039273/18880000000000000000 : ℝ)+2*(634660612191/377600000000000 : ℝ)*(14697/100000 : ℝ)=(400071940515157/400000000000000 : ℝ) by norm_num, show 1+2*(231613914676089/625000000000000000 : ℝ)=(312731613914676089/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18874067985298039273/18880000000000000000 : ℝ)*(X 1 0+X 2 0)+(634660612191/377600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (10921/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (18874067985298039273/18880000000000000000 : ℝ)) (alpha := (634660612191/377600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18874067985298039273/18880000000000000000 : ℝ)*(X 0 1+X 2 1)+(634660612191/377600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (10921/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (18874067985298039273/18880000000000000000 : ℝ)) (alpha := (634660612191/377600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18874067985298039273/18880000000000000000 : ℝ)*(X 0 2+X 1 2)+(634660612191/377600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (10921/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (18874067985298039273/18880000000000000000 : ℝ)) (alpha := (634660612191/377600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132348673/625000000 : ℝ)*X 0 0+(5397334413/10000000000 : ℝ)*X 0 1+(5261413339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336464943/2500000000 : ℝ)*X 1 0+(-273323243/1250000000 : ℝ)*X 1 1+(5261413343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42766879/80000000 : ℝ)*X 2 0+(2630706603/5000000000 : ℝ)*X 2 1+(-2186585987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174952691/5000000000 : ℝ)*X 0 0+(4214060959/10000000000 : ℝ)*X 0 1+(4489999597/10000000000 : ℝ)*X 0 2+(2174952691/5000000000 : ℝ)*X 1 0+(4214060959/10000000000 : ℝ)*X 1 1+(4489999597/10000000000 : ℝ)*X 1 2+(2174952691/5000000000 : ℝ)*X 2 0+(4214060959/10000000000 : ℝ)*X 2 1+(4489999597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2117584891/10000000000 : ℝ)*X 0 0+(1315447353/2500000000 : ℝ)*X 0 1+(674619607/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265558571/500000000 : ℝ)*X 1 0+(-2051042451/10000000000 : ℝ)*X 1 1+(2698478373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311171013/10000000000 : ℝ)*X 2 0+(2698478647/5000000000 : ℝ)*X 2 1+(-410208451/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349918017/10000000000 : ℝ)*X 0 0+(4489236417/10000000000 : ℝ)*X 0 1+(2107413501/5000000000 : ℝ)*X 0 2+(4349918017/10000000000 : ℝ)*X 1 0+(4489236417/10000000000 : ℝ)*X 1 1+(2107413501/5000000000 : ℝ)*X 1 2+(4349918017/10000000000 : ℝ)*X 2 0+(4489236417/10000000000 : ℝ)*X 2 1+(2107413501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8029034199295189811949/944000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222853171/12500000000000 : ℝ)*(base19) + (366065777/20000000000000 : ℝ)*(base23) + (70072997/25000000000000 : ℝ)*(upper3) + (25192709/50000000000000 : ℝ)*(upper4) + (86144873/50000000000000 : ℝ)*(upper5) + (54906678168243/1000000000000 : ℝ)*(major0) + (54906678168243/1000000000000 : ℝ)*(major1) + (54906678168243/1000000000000 : ℝ)*(major2) + (3678627333425649/50000000000000 : ℝ)*(sp0) + (1471458949882607/20000000000000 : ℝ)*(sp1) + (7357294701909517/100000000000000 : ℝ)*(sp2) + (1812007413813559/50000000000000 : ℝ)*(sp3) + (1308293347/3125000000000 : ℝ)*(sp4) + (5997567993/25000000000000 : ℝ)*(sp7) + (3624038817899091/100000000000000 : ℝ)*(f.failure) + (3678648266119201/50000000000000 : ℝ)*(f.sum) + (6535104776097/944000000000000000000000000 : ℝ)*base65 + (227294051053017339/18880000000000000000000000000000 : ℝ)*base67 + (277065457635622661/18880000000000000000000000000000 : ℝ)*base70 + (64456973450457339/18880000000000000000000000000000 : ℝ)*base71 + (5427482791041/944000000000000000000000000 : ℝ)*base73 + (339627678621542661/18880000000000000000000000000000 : ℝ)*base76 + (471584031011942661/18880000000000000000000000000000 : ℝ)*base78 + (189473246502617339/18880000000000000000000000000000 : ℝ)*base79 + (946981676719/944000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (71154261/10000000000000000000000 : ℝ)*base89 + (71154261/10000000000000000000000 : ℝ)*base91 + (71154261/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2386240268736259400836511919/472000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094989729/100000000000000 : ℝ)*(base19) + (130460951/20000000000000 : ℝ)*(base23) + (21053/2500000000000 : ℝ)*(upper2) + (330929099/100000000000000 : ℝ)*(upper3) + (8473871/25000000000000 : ℝ)*(upper5) + (2760601663103901/50000000000000 : ℝ)*(major0) + (2760601663103901/50000000000000 : ℝ)*(major1) + (2760601663103901/50000000000000 : ℝ)*(major2) + (3383383511/50000000000000 : ℝ)*(sp1) + (25547205937/100000000000000 : ℝ)*(sp2) + (7398213128329897/100000000000000 : ℝ)*(sp4) + (7398205266573147/100000000000000 : ℝ)*(sp5) + (3699093464409603/50000000000000 : ℝ)*(sp6) + (1822096677782951/50000000000000 : ℝ)*(sp7) + (1822096677782951/50000000000000 : ℝ)*(f.failure) + (7398213128329897/100000000000000 : ℝ)*(f.sum) + (17934473552989/9440000000000000000000000000 : ℝ)*base66 + (10068033715479946027/944000000000000000000000000000000 : ℝ)*base68 + (1511064679048053973/944000000000000000000000000000000 : ℝ)*base69 + (1432387544680053973/944000000000000000000000000000000 : ℝ)*base71 + (37852330165731/9440000000000000000000000000 : ℝ)*base73 + (24055618075895946027/944000000000000000000000000000000 : ℝ)*base76 + (7160897157895946027/944000000000000000000000000000000 : ℝ)*base78 + (35258430184247946027/944000000000000000000000000000000 : ℝ)*base80 + (50588019321891/9440000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (23156321/5000000000000000000000 : ℝ)*base89 + (23156321/5000000000000000000000 : ℝ)*base91 + (23156321/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1246_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10921/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1246_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1246_s5_0 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66188177/312500000 : ℝ)*x 0 + (84254909/156250000 : ℝ)*x 1 + (2633071237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66188177/312500000 : ℝ)^8439 ≤ (12880252201363/100000000000000 : ℝ)^6391 := by
    have hnat : (66188177 : ℕ)^8439*100000000000000^6391 ≤ 12880252201363^6391*312500000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66188177 312500000 12880252201363 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84254909/156250000 : ℝ)^8439 ≤ (5530092425777/12500000000000 : ℝ)^6391 := by
    have hnat : (84254909 : ℕ)^8439*12500000000000^6391 ≤ 5530092425777^6391*156250000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84254909 156250000 5530092425777 12500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633071237/5000000000 : ℝ)^8439 ≤ (42879008380453/100000000000000 : ℝ)^6391 := by
    have hnat : (2633071237 : ℕ)^8439*100000000000000^6391 ≤ 42879008380453^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633071237 5000000000 42879008380453 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66188177/312500000 : ℝ), (84254909/156250000 : ℝ), (2633071237/5000000000 : ℝ)] ![(12880252201363/100000000000000 : ℝ), (5530092425777/12500000000000 : ℝ), (42879008380453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66188177/312500000 : ℝ)|^8439 ≤ (12880252201363/100000000000000 : ℝ)^6391
        have hw : |(-66188177/312500000 : ℝ)|=(66188177/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84254909/156250000 : ℝ)|^8439 ≤ (5530092425777/12500000000000 : ℝ)^6391
        have hw : |(84254909/156250000 : ℝ)|=(84254909/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633071237/5000000000 : ℝ)|^8439 ≤ (42879008380453/100000000000000 : ℝ)^6391
        have hw : |(2633071237/5000000000 : ℝ)|=(2633071237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_1 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336147319/2500000000 : ℝ)*x 0 + (-2182009537/10000000000 : ℝ)*x 1 + (2633071237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336147319/2500000000 : ℝ)^8439 ≤ (21862222843057/50000000000000 : ℝ)^6391 := by
    have hnat : (1336147319 : ℕ)^8439*50000000000000^6391 ≤ 21862222843057^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336147319 2500000000 21862222843057 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182009537/10000000000 : ℝ)^8439 ≤ (13396545923451/100000000000000 : ℝ)^6391 := by
    have hnat : (2182009537 : ℕ)^8439*100000000000000^6391 ≤ 13396545923451^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182009537 10000000000 13396545923451 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633071237/5000000000 : ℝ)^8439 ≤ (42879008380453/100000000000000 : ℝ)^6391 := by
    have hnat : (2633071237 : ℕ)^8439*100000000000000^6391 ≤ 42879008380453^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633071237 5000000000 42879008380453 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336147319/2500000000 : ℝ), (-2182009537/10000000000 : ℝ), (2633071237/5000000000 : ℝ)] ![(21862222843057/50000000000000 : ℝ), (13396545923451/100000000000000 : ℝ), (42879008380453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336147319/2500000000 : ℝ)|^8439 ≤ (21862222843057/50000000000000 : ℝ)^6391
        have hw : |(1336147319/2500000000 : ℝ)|=(1336147319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2182009537/10000000000 : ℝ)|^8439 ≤ (13396545923451/100000000000000 : ℝ)^6391
        have hw : |(-2182009537/10000000000 : ℝ)|=(2182009537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633071237/5000000000 : ℝ)|^8439 ≤ (42879008380453/100000000000000 : ℝ)^6391
        have hw : |(2633071237/5000000000 : ℝ)|=(2633071237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_2 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672294637/5000000000 : ℝ)*x 0 + (5266142473/10000000000 : ℝ)*x 1 + (-109100477/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672294637/5000000000 : ℝ)^8439 ≤ (43724445664509/100000000000000 : ℝ)^6391 := by
    have hnat : (2672294637 : ℕ)^8439*100000000000000^6391 ≤ 43724445664509^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672294637 5000000000 43724445664509 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266142473/10000000000 : ℝ)^8439 ≤ (42879008369701/100000000000000 : ℝ)^6391 := by
    have hnat : (5266142473 : ℕ)^8439*100000000000000^6391 ≤ 42879008369701^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266142473 10000000000 42879008369701 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109100477/500000000 : ℝ)^8439 ≤ (3349136486943/25000000000000 : ℝ)^6391 := by
    have hnat : (109100477 : ℕ)^8439*25000000000000^6391 ≤ 3349136486943^6391*500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109100477 500000000 3349136486943 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672294637/5000000000 : ℝ), (5266142473/10000000000 : ℝ), (-109100477/500000000 : ℝ)] ![(43724445664509/100000000000000 : ℝ), (42879008369701/100000000000000 : ℝ), (3349136486943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672294637/5000000000 : ℝ)|^8439 ≤ (43724445664509/100000000000000 : ℝ)^6391
        have hw : |(2672294637/5000000000 : ℝ)|=(2672294637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266142473/10000000000 : ℝ)|^8439 ≤ (42879008369701/100000000000000 : ℝ)^6391
        have hw : |(5266142473/10000000000 : ℝ)|=(5266142473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109100477/500000000 : ℝ)|^8439 ≤ (3349136486943/25000000000000 : ℝ)^6391
        have hw : |(-109100477/500000000 : ℝ)|=(109100477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_3 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087541451/2500000000 : ℝ)*x 0 + (52799051/125000000 : ℝ)*x 1 + (4480069983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087541451/2500000000 : ℝ)^8439 ≤ (16658457004979/50000000000000 : ℝ)^6391 := by
    have hnat : (1087541451 : ℕ)^8439*50000000000000^6391 ≤ 16658457004979^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087541451 2500000000 16658457004979 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52799051/125000000 : ℝ)^8439 ≤ (16023101959759/50000000000000 : ℝ)^6391 := by
    have hnat : (52799051 : ℕ)^8439*50000000000000^6391 ≤ 16023101959759^6391*125000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52799051 125000000 16023101959759 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480069983/10000000000 : ℝ)^8439 ≤ (1385475282123/4000000000000 : ℝ)^6391 := by
    have hnat : (4480069983 : ℕ)^8439*4000000000000^6391 ≤ 1385475282123^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480069983 10000000000 1385475282123 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087541451/2500000000 : ℝ), (52799051/125000000 : ℝ), (4480069983/10000000000 : ℝ)] ![(16658457004979/50000000000000 : ℝ), (16023101959759/50000000000000 : ℝ), (1385475282123/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087541451/2500000000 : ℝ)|^8439 ≤ (16658457004979/50000000000000 : ℝ)^6391
        have hw : |(1087541451/2500000000 : ℝ)|=(1087541451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52799051/125000000 : ℝ)|^8439 ≤ (16023101959759/50000000000000 : ℝ)^6391
        have hw : |(52799051/125000000 : ℝ)|=(52799051/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480069983/10000000000 : ℝ)|^8439 ≤ (1385475282123/4000000000000 : ℝ)^6391
        have hw : |(4480069983/10000000000 : ℝ)|=(4480069983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_4 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118026579/10000000000 : ℝ)*x 0 + (2633233309/5000000000 : ℝ)*x 1 + (5391988833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118026579/10000000000 : ℝ)^8439 ≤ (6440145834441/50000000000000 : ℝ)^6391 := by
    have hnat : (2118026579 : ℕ)^8439*50000000000000^6391 ≤ 6440145834441^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118026579 10000000000 6440145834441 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633233309/5000000000 : ℝ)^8439 ≤ (21441246745539/50000000000000 : ℝ)^6391 := by
    have hnat : (2633233309 : ℕ)^8439*50000000000000^6391 ≤ 21441246745539^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633233309 5000000000 21441246745539 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391988833/10000000000 : ℝ)^8439 ≤ (11059303708067/25000000000000 : ℝ)^6391 := by
    have hnat : (5391988833 : ℕ)^8439*25000000000000^6391 ≤ 11059303708067^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391988833 10000000000 11059303708067 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118026579/10000000000 : ℝ), (2633233309/5000000000 : ℝ), (5391988833/10000000000 : ℝ)] ![(6440145834441/50000000000000 : ℝ), (21441246745539/50000000000000 : ℝ), (11059303708067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118026579/10000000000 : ℝ)|^8439 ≤ (6440145834441/50000000000000 : ℝ)^6391
        have hw : |(-2118026579/10000000000 : ℝ)|=(2118026579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633233309/5000000000 : ℝ)|^8439 ≤ (21441246745539/50000000000000 : ℝ)^6391
        have hw : |(2633233309/5000000000 : ℝ)|=(2633233309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391988833/10000000000 : ℝ)|^8439 ≤ (11059303708067/25000000000000 : ℝ)^6391
        have hw : |(5391988833/10000000000 : ℝ)|=(5391988833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_5 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265619381/500000000 : ℝ)*x 0 + (-2056163179/10000000000 : ℝ)*x 1 + (5391988833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265619381/500000000 : ℝ)^8439 ≤ (2711057329457/6250000000000 : ℝ)^6391 := by
    have hnat : (265619381 : ℕ)^8439*6250000000000^6391 ≤ 2711057329457^6391*500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265619381 500000000 2711057329457 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056163179/10000000000 : ℝ)^8439 ≤ (6192933941077/50000000000000 : ℝ)^6391 := by
    have hnat : (2056163179 : ℕ)^8439*50000000000000^6391 ≤ 6192933941077^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056163179 10000000000 6192933941077 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391988833/10000000000 : ℝ)^8439 ≤ (11059303708067/25000000000000 : ℝ)^6391 := by
    have hnat : (5391988833 : ℕ)^8439*25000000000000^6391 ≤ 11059303708067^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391988833 10000000000 11059303708067 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265619381/500000000 : ℝ), (-2056163179/10000000000 : ℝ), (5391988833/10000000000 : ℝ)] ![(2711057329457/6250000000000 : ℝ), (6192933941077/50000000000000 : ℝ), (11059303708067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265619381/500000000 : ℝ)|^8439 ≤ (2711057329457/6250000000000 : ℝ)^6391
        have hw : |(265619381/500000000 : ℝ)|=(265619381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056163179/10000000000 : ℝ)|^8439 ≤ (6192933941077/50000000000000 : ℝ)^6391
        have hw : |(-2056163179/10000000000 : ℝ)|=(2056163179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391988833/10000000000 : ℝ)|^8439 ≤ (11059303708067/25000000000000 : ℝ)^6391
        have hw : |(5391988833/10000000000 : ℝ)|=(5391988833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_6 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265619381/500000000 : ℝ)*x 0 + (5391988833/10000000000 : ℝ)*x 1 + (-2056163179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265619381/500000000 : ℝ)^8439 ≤ (2711057329457/6250000000000 : ℝ)^6391 := by
    have hnat : (265619381 : ℕ)^8439*6250000000000^6391 ≤ 2711057329457^6391*500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265619381 500000000 2711057329457 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391988833/10000000000 : ℝ)^8439 ≤ (11059303708067/25000000000000 : ℝ)^6391 := by
    have hnat : (5391988833 : ℕ)^8439*25000000000000^6391 ≤ 11059303708067^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391988833 10000000000 11059303708067 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056163179/10000000000 : ℝ)^8439 ≤ (6192933941077/50000000000000 : ℝ)^6391 := by
    have hnat : (2056163179 : ℕ)^8439*50000000000000^6391 ≤ 6192933941077^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056163179 10000000000 6192933941077 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265619381/500000000 : ℝ), (5391988833/10000000000 : ℝ), (-2056163179/10000000000 : ℝ)] ![(2711057329457/6250000000000 : ℝ), (11059303708067/25000000000000 : ℝ), (6192933941077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265619381/500000000 : ℝ)|^8439 ≤ (2711057329457/6250000000000 : ℝ)^6391
        have hw : |(265619381/500000000 : ℝ)|=(265619381/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391988833/10000000000 : ℝ)|^8439 ≤ (11059303708067/25000000000000 : ℝ)^6391
        have hw : |(5391988833/10000000000 : ℝ)|=(5391988833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056163179/10000000000 : ℝ)|^8439 ≤ (6192933941077/50000000000000 : ℝ)^6391
        have hw : |(-2056163179/10000000000 : ℝ)|=(2056163179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s5_7 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350175777/10000000000 : ℝ)*x 0 + (4479411921/10000000000 : ℝ)*x 1 + (168983383/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350175777/10000000000 : ℝ)^8439 ≤ (8329253716801/25000000000000 : ℝ)^6391 := by
    have hnat : (4350175777 : ℕ)^8439*25000000000000^6391 ≤ 8329253716801^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350175777 10000000000 8329253716801 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479411921/10000000000 : ℝ)^8439 ≤ (17315082082581/50000000000000 : ℝ)^6391 := by
    have hnat : (4479411921 : ℕ)^8439*50000000000000^6391 ≤ 17315082082581^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479411921 10000000000 17315082082581 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168983383/400000000 : ℝ)^8439 ≤ (32052820949041/100000000000000 : ℝ)^6391 := by
    have hnat : (168983383 : ℕ)^8439*100000000000000^6391 ≤ 32052820949041^6391*400000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168983383 400000000 32052820949041 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350175777/10000000000 : ℝ), (4479411921/10000000000 : ℝ), (168983383/400000000 : ℝ)] ![(8329253716801/25000000000000 : ℝ), (17315082082581/50000000000000 : ℝ), (32052820949041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350175777/10000000000 : ℝ)|^8439 ≤ (8329253716801/25000000000000 : ℝ)^6391
        have hw : |(4350175777/10000000000 : ℝ)|=(4350175777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479411921/10000000000 : ℝ)|^8439 ≤ (17315082082581/50000000000000 : ℝ)^6391
        have hw : |(4479411921/10000000000 : ℝ)|=(4479411921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168983383/400000000 : ℝ)|^8439 ≤ (32052820949041/100000000000000 : ℝ)^6391
        have hw : |(168983383/400000000 : ℝ)|=(168983383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1246_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11459/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3533/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5679/50000 : ℝ) ^ (4219/1024 : ℝ) ≤ (6407711924019453/50000000000000000000 : ℝ) := by
    have hpowers : (5679/50000 : ℝ)^4219 ≤ (6407711924019453/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5679 : ℕ)^4219*50000000000000000000^1024 ≤ 6407711924019453^1024*50000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5679 50000 6407711924019453 50000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5679/50000 : ℝ)) (X := (6407711924019453/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (4219/1024 : ℝ) ≤ (16253801586238941/50000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^4219 ≤ (16253801586238941/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14237 : ℕ)^4219*50000000000000000000^1024 ≤ 16253801586238941^1024*100000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 16253801586238941 50000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (16253801586238941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006407711924019453/25000000000000000000 : ℝ) ≤ (1250077753736837/1250000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (25006407711924019453/25000000000000000000 : ℝ)^1024 ≤ (1250077753736837/1250000000000000 : ℝ)^4219 := by
      have hnat : (25006407711924019453 : ℕ)^1024*1250000000000000^4219 ≤ 1250077753736837^4219*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006407711924019453 25000000000000000000 1250077753736837 1250000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250077753736837/1250000000000000 : ℝ)) (X := (25006407711924019453/25000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011330756755129197/25000000000000000000 : ℝ) ≤ (10001099853450783/10000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (25011330756755129197/25000000000000000000 : ℝ)^1024 ≤ (10001099853450783/10000000000000000 : ℝ)^4219 := by
      have hnat : (25011330756755129197 : ℕ)^1024*10000000000000000^4219 ≤ 10001099853450783^4219*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011330756755129197 25000000000000000000 10001099853450783 10000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001099853450783/10000000000000000 : ℝ)) (X := (25011330756755129197/25000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016253801586238941/25000000000000000000 : ℝ) ≤ (1000157767700687/1000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (25016253801586238941/25000000000000000000 : ℝ)^1024 ≤ (1000157767700687/1000000000000000 : ℝ)^4219 := by
      have hnat : (25016253801586238941 : ℕ)^1024*1000000000000000^4219 ≤ 1000157767700687^4219*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016253801586238941 25000000000000000000 1000157767700687 1000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000157767700687/1000000000000000 : ℝ)) (X := (25016253801586238941/25000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6407711924019453/50000000000000000000 : ℝ) ≤ ((7195234146041689373/7197500000000000000 : ℝ)+2*(477823556087/287900000000000 : ℝ)*(5679/50000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (7195234146041689373/7197500000000000000 : ℝ)+2*(477823556087/287900000000000 : ℝ)*(5679/50000 : ℝ)=(1250077753736837/1250000000000000 : ℝ) by norm_num, show 1+2*(6407711924019453/50000000000000000000 : ℝ)=(25006407711924019453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16253801586238941/50000000000000000000 : ℝ)+(6407711924019453/50000000000000000000 : ℝ) ≤ ((7195234146041689373/7197500000000000000 : ℝ)+(477823556087/287900000000000 : ℝ)*((14237/100000 : ℝ)+(5679/50000 : ℝ)))^(4219/1024 : ℝ) := by
    rw [show (7195234146041689373/7197500000000000000 : ℝ)+(477823556087/287900000000000 : ℝ)*((14237/100000 : ℝ)+(5679/50000 : ℝ))=(10001099853450783/10000000000000000 : ℝ) by norm_num, show 1+(16253801586238941/50000000000000000000 : ℝ)+(6407711924019453/50000000000000000000 : ℝ)=(25011330756755129197/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16253801586238941/50000000000000000000 : ℝ) ≤ ((7195234146041689373/7197500000000000000 : ℝ)+2*(477823556087/287900000000000 : ℝ)*(14237/100000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (7195234146041689373/7197500000000000000 : ℝ)+2*(477823556087/287900000000000 : ℝ)*(14237/100000 : ℝ)=(1000157767700687/1000000000000000 : ℝ) by norm_num, show 1+2*(16253801586238941/50000000000000000000 : ℝ)=(25016253801586238941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7195234146041689373/7197500000000000000 : ℝ)*(X 1 0+X 2 0)+(477823556087/287900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (7195234146041689373/7197500000000000000 : ℝ)) (alpha := (477823556087/287900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7195234146041689373/7197500000000000000 : ℝ)*(X 0 1+X 2 1)+(477823556087/287900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (7195234146041689373/7197500000000000000 : ℝ)) (alpha := (477823556087/287900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7195234146041689373/7197500000000000000 : ℝ)*(X 0 2+X 1 2)+(477823556087/287900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (5679/50000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (7195234146041689373/7197500000000000000 : ℝ)) (alpha := (477823556087/287900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66188177/312500000 : ℝ)*X 0 0+(84254909/156250000 : ℝ)*X 0 1+(2633071237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336147319/2500000000 : ℝ)*X 1 0+(-2182009537/10000000000 : ℝ)*X 1 1+(2633071237/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672294637/5000000000 : ℝ)*X 2 0+(5266142473/10000000000 : ℝ)*X 2 1+(-109100477/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087541451/2500000000 : ℝ)*X 0 0+(52799051/125000000 : ℝ)*X 0 1+(4480069983/10000000000 : ℝ)*X 0 2+(1087541451/2500000000 : ℝ)*X 1 0+(52799051/125000000 : ℝ)*X 1 1+(4480069983/10000000000 : ℝ)*X 1 2+(1087541451/2500000000 : ℝ)*X 2 0+(52799051/125000000 : ℝ)*X 2 1+(4480069983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2118026579/10000000000 : ℝ)*X 0 0+(2633233309/5000000000 : ℝ)*X 0 1+(5391988833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265619381/500000000 : ℝ)*X 1 0+(-2056163179/10000000000 : ℝ)*X 1 1+(5391988833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265619381/500000000 : ℝ)*X 2 0+(5391988833/10000000000 : ℝ)*X 2 1+(-2056163179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350175777/10000000000 : ℝ)*X 0 0+(4479411921/10000000000 : ℝ)*X 0 1+(168983383/400000000 : ℝ)*X 0 2+(4350175777/10000000000 : ℝ)*X 1 0+(4479411921/10000000000 : ℝ)*X 1 1+(168983383/400000000 : ℝ)*X 1 2+(4350175777/10000000000 : ℝ)*X 2 0+(4479411921/10000000000 : ℝ)*X 2 1+(168983383/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153903587470607291295669207/22492187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1328065549/100000000000000 : ℝ)*(base19) + (49225841/4000000000000 : ℝ)*(base23) + (50481579/100000000000000 : ℝ)*(lower2) + (176384597/100000000000000 : ℝ)*(upper3) + (393809/390625000000 : ℝ)*(upper5) + (739365207133069/12500000000000 : ℝ)*(major0) + (739365207133069/12500000000000 : ℝ)*(major1) + (739365207133069/12500000000000 : ℝ)*(major2) + (3962872744540271/50000000000000 : ℝ)*(sp0) + (7925780101881237/100000000000000 : ℝ)*(sp1) + (3962890099650381/50000000000000 : ℝ)*(sp2) + (244002640426939/6250000000000 : ℝ)*(sp3) + (7188173249/20000000000000 : ℝ)*(sp4) + (4852316693/25000000000000 : ℝ)*(sp7) + (976015414024449/25000000000000 : ℝ)*(f.failure) + (7925781429946787/100000000000000 : ℝ)*(f.sum) + (2597637498209/14395000000000000000000000000 : ℝ)*base65 + (429835346105938237/89968750000000000000000000000000 : ℝ)*base67 + (259681352804343013/89968750000000000000000000000000 : ℝ)*base70 + (57298635019749263/89968750000000000000000000000000 : ℝ)*base72 + (70403956829139/14395000000000000000000000000 : ℝ)*base73 + (3100689485437688237/89968750000000000000000000000000 : ℝ)*base75 + (105597670277000737/89968750000000000000000000000000 : ℝ)*base77 + (740984024684188237/89968750000000000000000000000000 : ℝ)*base79 + (21278064745071/3598750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14510921/2500000000000000000000 : ℝ)*base90 + (14510921/2500000000000000000000 : ℝ)*base92 + (14510921/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1359919471454213956361419617/179937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (678012173/50000000000000 : ℝ)*(base19) + (1473702933/100000000000000 : ℝ)*(base23) + (152245183/100000000000000 : ℝ)*(upper3) + (26764619/50000000000000 : ℝ)*(lower4) + (154700543/100000000000000 : ℝ)*(upper5) + (2972735326691819/50000000000000 : ℝ)*(major0) + (2972735326691819/50000000000000 : ℝ)*(major1) + (2972735326691819/50000000000000 : ℝ)*(major2) + (18777354931/50000000000000 : ℝ)*(sp1) + (5043163907/12500000000000 : ℝ)*(sp2) + (398335797960713/5000000000000 : ℝ)*(sp4) + (1991669262120013/25000000000000 : ℝ)*(sp5) + (796667414020007/10000000000000 : ℝ)*(sp6) + (245264068476787/6250000000000 : ℝ)*(sp7) + (245264068476787/6250000000000 : ℝ)*(f.failure) + (398335797960713/5000000000000 : ℝ)*(f.sum) + (55538652554063/7197500000000000000000000000 : ℝ)*base65 + (4457655086323664487/359875000000000000000000000000000 : ℝ)*base67 + (2384016085477164487/359875000000000000000000000000000 : ℝ)*base69 + (5699333877461664487/359875000000000000000000000000000 : ℝ)*base71 + (806276198479/224921875000000000000000000 : ℝ)*base73 + (2507172751252664487/359875000000000000000000000000000 : ℝ)*base75 + (1596109162015664487/359875000000000000000000000000000 : ℝ)*base77 + (6022095870558414487/359875000000000000000000000000000 : ℝ)*base79 + (1176783667167/449843750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2996523/625000000000000000000 : ℝ)*base90 + (2996523/625000000000000000000 : ℝ)*base92 + (2996523/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1246_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1246_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1246_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1246_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1246_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1246_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11459/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1246_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
