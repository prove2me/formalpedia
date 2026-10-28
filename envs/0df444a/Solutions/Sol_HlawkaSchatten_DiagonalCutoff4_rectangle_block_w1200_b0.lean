-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1200_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:01.603948+00:00
-- url     : https://prove2.me/submissions/be03f661-cf6e-4301-a14a-30d1d9bab227

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
theorem support_rectangle_w1200_s0_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1170993/6250000 : ℝ)*x 0 + (1208204341/2000000000 : ℝ)*x 1 + (4787763649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1170993/6250000 : ℝ)^8393 ≤ (1091220630797/10000000000000 : ℝ)^6345 := by
    have hnat : (1170993 : ℕ)^8393*10000000000000^6345 ≤ 1091220630797^6345*6250000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170993 6250000 1091220630797 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208204341/2000000000 : ℝ)^8393 ≤ (51340318509307/100000000000000 : ℝ)^6345 := by
    have hnat : (1208204341 : ℕ)^8393*100000000000000^6345 ≤ 51340318509307^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208204341 2000000000 51340318509307 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787763649/10000000000 : ℝ)^8393 ≤ (2359217197813/6250000000000 : ℝ)^6345 := by
    have hnat : (4787763649 : ℕ)^8393*6250000000000^6345 ≤ 2359217197813^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787763649 10000000000 2359217197813 6250000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1170993/6250000 : ℝ), (1208204341/2000000000 : ℝ), (4787763649/10000000000 : ℝ)] ![(1091220630797/10000000000000 : ℝ), (51340318509307/100000000000000 : ℝ), (2359217197813/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1170993/6250000 : ℝ)|^8393 ≤ (1091220630797/10000000000000 : ℝ)^6345
        have hw : |(-1170993/6250000 : ℝ)|=(1170993/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208204341/2000000000 : ℝ)|^8393 ≤ (51340318509307/100000000000000 : ℝ)^6345
        have hw : |(1208204341/2000000000 : ℝ)|=(1208204341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787763649/10000000000 : ℝ)|^8393 ≤ (2359217197813/6250000000000 : ℝ)^6345
        have hw : |(4787763649/10000000000 : ℝ)|=(4787763649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5513525823/10000000000 : ℝ)*x 0 + (-2591197351/10000000000 : ℝ)*x 1 + (2393881819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513525823/10000000000 : ℝ)^8393 ≤ (45495620465591/100000000000000 : ℝ)^6345 := by
    have hnat : (5513525823 : ℕ)^8393*100000000000000^6345 ≤ 45495620465591^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513525823 10000000000 45495620465591 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591197351/10000000000 : ℝ)^8393 ≤ (8378452233709/50000000000000 : ℝ)^6345 := by
    have hnat : (2591197351 : ℕ)^8393*50000000000000^6345 ≤ 8378452233709^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591197351 10000000000 8378452233709 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393881819/5000000000 : ℝ)^8393 ≤ (37747475050289/100000000000000 : ℝ)^6345 := by
    have hnat : (2393881819 : ℕ)^8393*100000000000000^6345 ≤ 37747475050289^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393881819 5000000000 37747475050289 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513525823/10000000000 : ℝ), (-2591197351/10000000000 : ℝ), (2393881819/5000000000 : ℝ)] ![(45495620465591/100000000000000 : ℝ), (8378452233709/50000000000000 : ℝ), (37747475050289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513525823/10000000000 : ℝ)|^8393 ≤ (45495620465591/100000000000000 : ℝ)^6345
        have hw : |(5513525823/10000000000 : ℝ)|=(5513525823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2591197351/10000000000 : ℝ)|^8393 ≤ (8378452233709/50000000000000 : ℝ)^6345
        have hw : |(-2591197351/10000000000 : ℝ)|=(2591197351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2393881819/5000000000 : ℝ)|^8393 ≤ (37747475050289/100000000000000 : ℝ)^6345
        have hw : |(2393881819/5000000000 : ℝ)|=(2393881819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378381453/2500000000 : ℝ)*x 0 + (4787763651/10000000000 : ℝ)*x 1 + (-51823947/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378381453/2500000000 : ℝ)^8393 ≤ (1819824813821/4000000000000 : ℝ)^6345 := by
    have hnat : (1378381453 : ℕ)^8393*4000000000000^6345 ≤ 1819824813821^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378381453 2500000000 1819824813821 4000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787763651/10000000000 : ℝ)^8393 ≤ (18873737592933/50000000000000 : ℝ)^6345 := by
    have hnat : (4787763651 : ℕ)^8393*50000000000000^6345 ≤ 18873737592933^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787763651 10000000000 18873737592933 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51823947/200000000 : ℝ)^8393 ≤ (16756904458863/100000000000000 : ℝ)^6345 := by
    have hnat : (51823947 : ℕ)^8393*100000000000000^6345 ≤ 16756904458863^6345*200000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51823947 200000000 16756904458863 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378381453/2500000000 : ℝ), (4787763651/10000000000 : ℝ), (-51823947/200000000 : ℝ)] ![(1819824813821/4000000000000 : ℝ), (18873737592933/50000000000000 : ℝ), (16756904458863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378381453/2500000000 : ℝ)|^8393 ≤ (1819824813821/4000000000000 : ℝ)^6345
        have hw : |(1378381453/2500000000 : ℝ)|=(1378381453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787763651/10000000000 : ℝ)|^8393 ≤ (18873737592933/50000000000000 : ℝ)^6345
        have hw : |(4787763651/10000000000 : ℝ)|=(4787763651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51823947/200000000 : ℝ)|^8393 ≤ (16756904458863/100000000000000 : ℝ)^6345
        have hw : |(-51823947/200000000 : ℝ)|=(51823947/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2098170133/5000000000 : ℝ)*x 0 + (1559271337/5000000000 : ℝ)*x 1 + (5640263529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098170133/5000000000 : ℝ)^8393 ≤ (3963266137743/12500000000000 : ℝ)^6345 := by
    have hnat : (2098170133 : ℕ)^8393*12500000000000^6345 ≤ 3963266137743^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098170133 5000000000 3963266137743 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559271337/5000000000 : ℝ)^8393 ≤ (21409796366939/100000000000000 : ℝ)^6345 := by
    have hnat : (1559271337 : ℕ)^8393*100000000000000^6345 ≤ 21409796366939^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559271337 5000000000 21409796366939 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5640263529/10000000000 : ℝ)^8393 ≤ (46884074514189/100000000000000 : ℝ)^6345 := by
    have hnat : (5640263529 : ℕ)^8393*100000000000000^6345 ≤ 46884074514189^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5640263529 10000000000 46884074514189 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098170133/5000000000 : ℝ), (1559271337/5000000000 : ℝ), (5640263529/10000000000 : ℝ)] ![(3963266137743/12500000000000 : ℝ), (21409796366939/100000000000000 : ℝ), (46884074514189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098170133/5000000000 : ℝ)|^8393 ≤ (3963266137743/12500000000000 : ℝ)^6345
        have hw : |(2098170133/5000000000 : ℝ)|=(2098170133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559271337/5000000000 : ℝ)|^8393 ≤ (21409796366939/100000000000000 : ℝ)^6345
        have hw : |(1559271337/5000000000 : ℝ)|=(1559271337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5640263529/10000000000 : ℝ)|^8393 ≤ (46884074514189/100000000000000 : ℝ)^6345
        have hw : |(5640263529/10000000000 : ℝ)|=(5640263529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-469641533/2500000000 : ℝ)*x 0 + (4820063807/10000000000 : ℝ)*x 1 + (750947737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469641533/2500000000 : ℝ)^8393 ≤ (2737642194013/25000000000000 : ℝ)^6345 := by
    have hnat : (469641533 : ℕ)^8393*25000000000000^6345 ≤ 2737642194013^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469641533 2500000000 2737642194013 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820063807/10000000000 : ℝ)^8393 ≤ (19042349135907/50000000000000 : ℝ)^6345 := by
    have hnat : (4820063807 : ℕ)^8393*50000000000000^6345 ≤ 19042349135907^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820063807 10000000000 19042349135907 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750947737/1250000000 : ℝ)^8393 ≤ (50964732928703/100000000000000 : ℝ)^6345 := by
    have hnat : (750947737 : ℕ)^8393*100000000000000^6345 ≤ 50964732928703^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750947737 1250000000 50964732928703 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-469641533/2500000000 : ℝ), (4820063807/10000000000 : ℝ), (750947737/1250000000 : ℝ)] ![(2737642194013/25000000000000 : ℝ), (19042349135907/50000000000000 : ℝ), (50964732928703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-469641533/2500000000 : ℝ)|^8393 ≤ (2737642194013/25000000000000 : ℝ)^6345
        have hw : |(-469641533/2500000000 : ℝ)|=(469641533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820063807/10000000000 : ℝ)|^8393 ≤ (19042349135907/50000000000000 : ℝ)^6345
        have hw : |(4820063807/10000000000 : ℝ)|=(4820063807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750947737/1250000000 : ℝ)|^8393 ≤ (50964732928703/100000000000000 : ℝ)^6345
        have hw : |(750947737/1250000000 : ℝ)|=(750947737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586357679/5000000000 : ℝ)*x 0 + (-3428447/25000000 : ℝ)*x 1 + (6007583631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586357679/5000000000 : ℝ)^8393 ≤ (41813298477949/100000000000000 : ℝ)^6345 := by
    have hnat : (2586357679 : ℕ)^8393*100000000000000^6345 ≤ 41813298477949^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586357679 5000000000 41813298477949 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3428447/25000000 : ℝ)^8393 ≤ (1805487279611/25000000000000 : ℝ)^6345 := by
    have hnat : (3428447 : ℕ)^8393*25000000000000^6345 ≤ 1805487279611^6345*25000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3428447 25000000 1805487279611 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6007583631/10000000000 : ℝ)^8393 ≤ (25482376199109/50000000000000 : ℝ)^6345 := by
    have hnat : (6007583631 : ℕ)^8393*50000000000000^6345 ≤ 25482376199109^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6007583631 10000000000 25482376199109 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586357679/5000000000 : ℝ), (-3428447/25000000 : ℝ), (6007583631/10000000000 : ℝ)] ![(41813298477949/100000000000000 : ℝ), (1805487279611/25000000000000 : ℝ), (25482376199109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586357679/5000000000 : ℝ)|^8393 ≤ (41813298477949/100000000000000 : ℝ)^6345
        have hw : |(2586357679/5000000000 : ℝ)|=(2586357679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3428447/25000000 : ℝ)|^8393 ≤ (1805487279611/25000000000000 : ℝ)^6345
        have hw : |(-3428447/25000000 : ℝ)|=(3428447/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6007583631/10000000000 : ℝ)|^8393 ≤ (25482376199109/50000000000000 : ℝ)^6345
        have hw : |(6007583631/10000000000 : ℝ)|=(6007583631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2586358521/5000000000 : ℝ)*x 0 + (600758249/1000000000 : ℝ)*x 1 + (-342844513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586358521/5000000000 : ℝ)^8393 ≤ (41813316484211/100000000000000 : ℝ)^6345 := by
    have hnat : (2586358521 : ℕ)^8393*100000000000000^6345 ≤ 41813316484211^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586358521 5000000000 41813316484211 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600758249/1000000000 : ℝ)^8393 ≤ (25482369797173/50000000000000 : ℝ)^6345 := by
    have hnat : (600758249 : ℕ)^8393*50000000000000^6345 ≤ 25482369797173^6345*1000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600758249 1000000000 25482369797173 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342844513/2500000000 : ℝ)^8393 ≤ (7221943907887/100000000000000 : ℝ)^6345 := by
    have hnat : (342844513 : ℕ)^8393*100000000000000^6345 ≤ 7221943907887^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342844513 2500000000 7221943907887 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586358521/5000000000 : ℝ), (600758249/1000000000 : ℝ), (-342844513/2500000000 : ℝ)] ![(41813316484211/100000000000000 : ℝ), (25482369797173/50000000000000 : ℝ), (7221943907887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586358521/5000000000 : ℝ)|^8393 ≤ (41813316484211/100000000000000 : ℝ)^6345
        have hw : |(2586358521/5000000000 : ℝ)|=(2586358521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600758249/1000000000 : ℝ)|^8393 ≤ (25482369797173/50000000000000 : ℝ)^6345
        have hw : |(600758249/1000000000 : ℝ)|=(600758249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342844513/2500000000 : ℝ)|^8393 ≤ (7221943907887/100000000000000 : ℝ)^6345
        have hw : |(-342844513/2500000000 : ℝ)|=(342844513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s0_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4206354963/10000000000 : ℝ)*x 0 + (1393818671/2500000000 : ℝ)*x 1 + (3185824039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206354963/10000000000 : ℝ)^8393 ≤ (15903129420747/50000000000000 : ℝ)^6345 := by
    have hnat : (4206354963 : ℕ)^8393*50000000000000^6345 ≤ 15903129420747^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206354963 10000000000 15903129420747 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393818671/2500000000 : ℝ)^8393 ≤ (46170827588753/100000000000000 : ℝ)^6345 := by
    have hnat : (1393818671 : ℕ)^8393*100000000000000^6345 ≤ 46170827588753^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393818671 2500000000 46170827588753 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185824039/10000000000 : ℝ)^8393 ≤ (22022913551689/100000000000000 : ℝ)^6345 := by
    have hnat : (3185824039 : ℕ)^8393*100000000000000^6345 ≤ 22022913551689^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185824039 10000000000 22022913551689 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206354963/10000000000 : ℝ), (1393818671/2500000000 : ℝ), (3185824039/10000000000 : ℝ)] ![(15903129420747/50000000000000 : ℝ), (46170827588753/100000000000000 : ℝ), (22022913551689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206354963/10000000000 : ℝ)|^8393 ≤ (15903129420747/50000000000000 : ℝ)^6345
        have hw : |(4206354963/10000000000 : ℝ)|=(4206354963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393818671/2500000000 : ℝ)|^8393 ≤ (46170827588753/100000000000000 : ℝ)^6345
        have hw : |(1393818671/2500000000 : ℝ)|=(1393818671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185824039/10000000000 : ℝ)|^8393 ≤ (22022913551689/100000000000000 : ℝ)^6345
        have hw : |(3185824039/10000000000 : ℝ)|=(3185824039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (13/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13797/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1049/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1049 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1049*1^256 ≤ 0^256*1^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1049/256 : ℝ) ≤ (1170438612628189759/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1049 ≤ (1170438612628189759/50000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1049*50000000000000000000^256 ≤ 1170438612628189759^256*5^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1170438612628189759 50000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1170438612628189759/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1049 := by
      have hnat : (1 : ℕ)^256*1^1049 ≤ 1^1049*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (51170438612628189759/50000000000000000000 : ℝ) ≤ (1257078571978391/1250000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (51170438612628189759/50000000000000000000 : ℝ)^256 ≤ (1257078571978391/1250000000000000 : ℝ)^1049 := by
      have hnat : (51170438612628189759 : ℕ)^256*1250000000000000^1049 ≤ 1257078571978391^1049*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51170438612628189759 50000000000000000000 1257078571978391 1250000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257078571978391/1250000000000000 : ℝ)) (X := (51170438612628189759/50000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (26170438612628189759/25000000000000000000 : ℝ) ≤ (632078571978391/625000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (26170438612628189759/25000000000000000000 : ℝ)^256 ≤ (632078571978391/625000000000000 : ℝ)^1049 := by
      have hnat : (26170438612628189759 : ℕ)^256*625000000000000^1049 ≤ 632078571978391^1049*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26170438612628189759 25000000000000000000 632078571978391 625000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632078571978391/625000000000000 : ℝ)) (X := (26170438612628189759/25000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7078571978391/500000000000000 : ℝ)*(0 : ℝ))^(1049/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(7078571978391/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1170438612628189759/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7078571978391/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (1 : ℝ)+(7078571978391/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257078571978391/1250000000000000 : ℝ) by norm_num, show 1+(1170438612628189759/50000000000000000000 : ℝ)+(0 : ℝ)=(51170438612628189759/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1170438612628189759/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7078571978391/500000000000000 : ℝ)*(2/5 : ℝ))^(1049/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(7078571978391/500000000000000 : ℝ)*(2/5 : ℝ)=(632078571978391/625000000000000 : ℝ) by norm_num, show 1+2*(1170438612628189759/50000000000000000000 : ℝ)=(26170438612628189759/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7078571978391/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7078571978391/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7078571978391/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7078571978391/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7078571978391/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7078571978391/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1170993/6250000 : ℝ)*X 0 0+(1208204341/2000000000 : ℝ)*X 0 1+(4787763649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513525823/10000000000 : ℝ)*X 1 0+(-2591197351/10000000000 : ℝ)*X 1 1+(2393881819/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1378381453/2500000000 : ℝ)*X 2 0+(4787763651/10000000000 : ℝ)*X 2 1+(-51823947/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098170133/5000000000 : ℝ)*X 0 0+(1559271337/5000000000 : ℝ)*X 0 1+(5640263529/10000000000 : ℝ)*X 0 2+(2098170133/5000000000 : ℝ)*X 1 0+(1559271337/5000000000 : ℝ)*X 1 1+(5640263529/10000000000 : ℝ)*X 1 2+(2098170133/5000000000 : ℝ)*X 2 0+(1559271337/5000000000 : ℝ)*X 2 1+(5640263529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-469641533/2500000000 : ℝ)*X 0 0+(4820063807/10000000000 : ℝ)*X 0 1+(750947737/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586357679/5000000000 : ℝ)*X 1 0+(-3428447/25000000 : ℝ)*X 1 1+(6007583631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586358521/5000000000 : ℝ)*X 2 0+(600758249/1000000000 : ℝ)*X 2 1+(-342844513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206354963/10000000000 : ℝ)*X 0 0+(1393818671/2500000000 : ℝ)*X 0 1+(3185824039/10000000000 : ℝ)*X 0 2+(4206354963/10000000000 : ℝ)*X 1 0+(1393818671/2500000000 : ℝ)*X 1 1+(3185824039/10000000000 : ℝ)*X 1 2+(4206354963/10000000000 : ℝ)*X 2 0+(1393818671/2500000000 : ℝ)*X 2 1+(3185824039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94758240400149534131931/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5164781/12500000000000 : ℝ)*(base1) + (232572319/25000000000000 : ℝ)*(base19) + (108109409/12500000000000 : ℝ)*(base23) + (6382207/10000000000000 : ℝ)*(base24) + (106474417/50000000000000 : ℝ)*(upper3) + (597241387149353/100000000000000 : ℝ)*(major0) + (597241387149353/100000000000000 : ℝ)*(major1) + (597241387149353/100000000000000 : ℝ)*(major2) + (797923408365899/100000000000000 : ℝ)*(sp0) + (797924496737451/100000000000000 : ℝ)*(sp1) + (99740562291173/12500000000000 : ℝ)*(sp2) + (19827777554261/5000000000000 : ℝ)*(sp3) + (82399163/4000000000000 : ℝ)*(sp4) + (407131047/25000000000000 : ℝ)*(sp7) + (49569652615957/12500000000000 : ℝ)*(f.failure) + (398962713513363/50000000000000 : ℝ)*(f.sum) + (10440855968977/25000000000000000000000000000 : ℝ)*base66 + (68608446031023/50000000000000000000000000000 : ℝ)*base67 + (291202587481023/50000000000000000000000000000 : ℝ)*base69 + (51703468781023/50000000000000000000000000000 : ℝ)*base71 + (20297058643977/25000000000000000000000000000 : ℝ)*base74 + (43716166868977/50000000000000000000000000000 : ℝ)*base76 + (340585337031023/50000000000000000000000000000 : ℝ)*base77 + (172871212831023/50000000000000000000000000000 : ℝ)*base79 + (38019897831023/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (317577/125000000000000000000 : ℝ)*base89 + (317577/125000000000000000000 : ℝ)*base91 + (317577/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357994242068929599/100000000000000000000000 : ℝ) := by norm_num
    linear_combination (13954833/100000000000000 : ℝ)*(base1) + (681120499/100000000000000 : ℝ)*(base19) + (258404937/25000000000000 : ℝ)*(base23) + (237970573/100000000000000 : ℝ)*(upper3) + (7193487/50000000000000 : ℝ)*(upper5) + (630299275110897/100000000000000 : ℝ)*(major0) + (630299275110897/100000000000000 : ℝ)*(major1) + (630299275110897/100000000000000 : ℝ)*(major2) + (1407424589/100000000000000 : ℝ)*(sp1) + (2596656049/100000000000000 : ℝ)*(sp2) + (842091398500499/100000000000000 : ℝ)*(sp4) + (421044648000289/50000000000000 : ℝ)*(sp5) + (842087754269869/100000000000000 : ℝ)*(sp6) + (418507032389877/100000000000000 : ℝ)*(sp7) + (41850704634471/10000000000000 : ℝ)*(f.failure) + (421045692272833/50000000000000 : ℝ)*(f.sum) + (41222029448273/25000000000000000000000000000 : ℝ)*base66 + (327497534576727/50000000000000000000000000000 : ℝ)*base67 + (99947752723273/50000000000000000000000000000 : ℝ)*base70 + (46839198473273/50000000000000000000000000000 : ℝ)*base72 + (29114119401727/25000000000000000000000000000 : ℝ)*base73 + (36988877476727/50000000000000000000000000000 : ℝ)*base75 + (77325520776727/50000000000000000000000000000 : ℝ)*base77 + (128041083776727/50000000000000000000000000000 : ℝ)*base79 + (122263483998273/25000000000000000000000000000 : ℝ)*base82 + (354669/100000000000000000000 : ℝ)*base90 + (354669/100000000000000000000 : ℝ)*base92 + (354669/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1200_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13797/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1200_s1_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-518513639/2500000000 : ℝ)*x 0 + (2843139179/5000000000 : ℝ)*x 1 + (2507091947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518513639/2500000000 : ℝ)^8393 ≤ (3120668311151/25000000000000 : ℝ)^6345 := by
    have hnat : (518513639 : ℕ)^8393*25000000000000^6345 ≤ 3120668311151^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518513639 2500000000 3120668311151 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2843139179/5000000000 : ℝ)^8393 ≤ (23695345749361/50000000000000 : ℝ)^6345 := by
    have hnat : (2843139179 : ℕ)^8393*50000000000000^6345 ≤ 23695345749361^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843139179 5000000000 23695345749361 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2507091947/5000000000 : ℝ)^8393 ≤ (40126635242479/100000000000000 : ℝ)^6345 := by
    have hnat : (2507091947 : ℕ)^8393*100000000000000^6345 ≤ 40126635242479^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507091947 5000000000 40126635242479 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-518513639/2500000000 : ℝ), (2843139179/5000000000 : ℝ), (2507091947/5000000000 : ℝ)] ![(3120668311151/25000000000000 : ℝ), (23695345749361/50000000000000 : ℝ), (40126635242479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-518513639/2500000000 : ℝ)|^8393 ≤ (3120668311151/25000000000000 : ℝ)^6345
        have hw : |(-518513639/2500000000 : ℝ)|=(518513639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2843139179/5000000000 : ℝ)|^8393 ≤ (23695345749361/50000000000000 : ℝ)^6345
        have hw : |(2843139179/5000000000 : ℝ)|=(2843139179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2507091947/5000000000 : ℝ)|^8393 ≤ (40126635242479/100000000000000 : ℝ)^6345
        have hw : |(2507091947/5000000000 : ℝ)|=(2507091947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5415944461/10000000000 : ℝ)*x 0 + (-1217848763/5000000000 : ℝ)*x 1 + (156693259/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415944461/10000000000 : ℝ)^8393 ≤ (1110839235673/2500000000000 : ℝ)^6345 := by
    have hnat : (5415944461 : ℕ)^8393*2500000000000^6345 ≤ 1110839235673^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415944461 10000000000 1110839235673 2500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217848763/5000000000 : ℝ)^8393 ≤ (15439791146711/100000000000000 : ℝ)^6345 := by
    have hnat : (1217848763 : ℕ)^8393*100000000000000^6345 ≤ 15439791146711^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217848763 5000000000 15439791146711 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156693259/312500000 : ℝ)^8393 ≤ (4012663941323/10000000000000 : ℝ)^6345 := by
    have hnat : (156693259 : ℕ)^8393*10000000000000^6345 ≤ 4012663941323^6345*312500000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156693259 312500000 4012663941323 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415944461/10000000000 : ℝ), (-1217848763/5000000000 : ℝ), (156693259/312500000 : ℝ)] ![(1110839235673/2500000000000 : ℝ), (15439791146711/100000000000000 : ℝ), (4012663941323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415944461/10000000000 : ℝ)|^8393 ≤ (1110839235673/2500000000000 : ℝ)^6345
        have hw : |(5415944461/10000000000 : ℝ)|=(5415944461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1217848763/5000000000 : ℝ)|^8393 ≤ (15439791146711/100000000000000 : ℝ)^6345
        have hw : |(-1217848763/5000000000 : ℝ)|=(1217848763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156693259/312500000 : ℝ)|^8393 ≤ (4012663941323/10000000000000 : ℝ)^6345
        have hw : |(156693259/312500000 : ℝ)|=(156693259/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (676992919/1250000000 : ℝ)*x 0 + (1002837/2000000 : ℝ)*x 1 + (-1217849031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676992919/1250000000 : ℝ)^8393 ≤ (44433557391697/100000000000000 : ℝ)^6345 := by
    have hnat : (676992919 : ℕ)^8393*100000000000000^6345 ≤ 44433557391697^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676992919 1250000000 44433557391697 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002837/2000000 : ℝ)^8393 ≤ (40126646950223/100000000000000 : ℝ)^6345 := by
    have hnat : (1002837 : ℕ)^8393*100000000000000^6345 ≤ 40126646950223^6345*2000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002837 2000000 40126646950223 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217849031/5000000000 : ℝ)^8393 ≤ (7719897820539/50000000000000 : ℝ)^6345 := by
    have hnat : (1217849031 : ℕ)^8393*50000000000000^6345 ≤ 7719897820539^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217849031 5000000000 7719897820539 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676992919/1250000000 : ℝ), (1002837/2000000 : ℝ), (-1217849031/5000000000 : ℝ)] ![(44433557391697/100000000000000 : ℝ), (40126646950223/100000000000000 : ℝ), (7719897820539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676992919/1250000000 : ℝ)|^8393 ≤ (44433557391697/100000000000000 : ℝ)^6345
        have hw : |(676992919/1250000000 : ℝ)|=(676992919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002837/2000000 : ℝ)|^8393 ≤ (40126646950223/100000000000000 : ℝ)^6345
        have hw : |(1002837/2000000 : ℝ)|=(1002837/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217849031/5000000000 : ℝ)|^8393 ≤ (7719897820539/50000000000000 : ℝ)^6345
        have hw : |(-1217849031/5000000000 : ℝ)|=(1217849031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312487121/10000000000 : ℝ)*x 0 + (737563989/2000000000 : ℝ)*x 1 + (5040163359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312487121/10000000000 : ℝ)^8393 ≤ (32872104197697/100000000000000 : ℝ)^6345 := by
    have hnat : (4312487121 : ℕ)^8393*100000000000000^6345 ≤ 32872104197697^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312487121 10000000000 32872104197697 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737563989/2000000000 : ℝ)^8393 ≤ (13363010493807/50000000000000 : ℝ)^6345 := by
    have hnat : (737563989 : ℕ)^8393*50000000000000^6345 ≤ 13363010493807^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737563989 2000000000 13363010493807 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5040163359/10000000000 : ℝ)^8393 ≤ (8080374960951/20000000000000 : ℝ)^6345 := by
    have hnat : (5040163359 : ℕ)^8393*20000000000000^6345 ≤ 8080374960951^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5040163359 10000000000 8080374960951 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312487121/10000000000 : ℝ), (737563989/2000000000 : ℝ), (5040163359/10000000000 : ℝ)] ![(32872104197697/100000000000000 : ℝ), (13363010493807/50000000000000 : ℝ), (8080374960951/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312487121/10000000000 : ℝ)|^8393 ≤ (32872104197697/100000000000000 : ℝ)^6345
        have hw : |(4312487121/10000000000 : ℝ)|=(4312487121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737563989/2000000000 : ℝ)|^8393 ≤ (13363010493807/50000000000000 : ℝ)^6345
        have hw : |(737563989/2000000000 : ℝ)|=(737563989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5040163359/10000000000 : ℝ)|^8393 ≤ (8080374960951/20000000000000 : ℝ)^6345
        have hw : |(5040163359/10000000000 : ℝ)|=(5040163359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074781697/10000000000 : ℝ)*x 0 + (502315791/1000000000 : ℝ)*x 1 + (5677131399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074781697/10000000000 : ℝ)^8393 ≤ (12488462413581/100000000000000 : ℝ)^6345 := by
    have hnat : (2074781697 : ℕ)^8393*100000000000000^6345 ≤ 12488462413581^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074781697 10000000000 12488462413581 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502315791/1000000000 : ℝ)^8393 ≤ (40221658583243/100000000000000 : ℝ)^6345 := by
    have hnat : (502315791 : ℕ)^8393*100000000000000^6345 ≤ 40221658583243^6345*1000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502315791 1000000000 40221658583243 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5677131399/10000000000 : ℝ)^8393 ≤ (9457975796367/20000000000000 : ℝ)^6345 := by
    have hnat : (5677131399 : ℕ)^8393*20000000000000^6345 ≤ 9457975796367^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677131399 10000000000 9457975796367 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074781697/10000000000 : ℝ), (502315791/1000000000 : ℝ), (5677131399/10000000000 : ℝ)] ![(12488462413581/100000000000000 : ℝ), (40221658583243/100000000000000 : ℝ), (9457975796367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074781697/10000000000 : ℝ)|^8393 ≤ (12488462413581/100000000000000 : ℝ)^6345
        have hw : |(-2074781697/10000000000 : ℝ)|=(2074781697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502315791/1000000000 : ℝ)|^8393 ≤ (40221658583243/100000000000000 : ℝ)^6345
        have hw : |(502315791/1000000000 : ℝ)|=(502315791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5677131399/10000000000 : ℝ)|^8393 ≤ (9457975796367/20000000000000 : ℝ)^6345
        have hw : |(5677131399/10000000000 : ℝ)|=(5677131399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5243139173/10000000000 : ℝ)*x 0 + (-354550323/2000000000 : ℝ)*x 1 + (5677130307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243139173/10000000000 : ℝ)^8393 ≤ (4256795836643/10000000000000 : ℝ)^6345 := by
    have hnat : (5243139173 : ℕ)^8393*10000000000000^6345 ≤ 4256795836643^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243139173 10000000000 4256795836643 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354550323/2000000000 : ℝ)^8393 ≤ (5071087333287/50000000000000 : ℝ)^6345 := by
    have hnat : (354550323 : ℕ)^8393*50000000000000^6345 ≤ 5071087333287^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354550323 2000000000 5071087333287 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5677130307/10000000000 : ℝ)^8393 ≤ (738904171087/1562500000000 : ℝ)^6345 := by
    have hnat : (5677130307 : ℕ)^8393*1562500000000^6345 ≤ 738904171087^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5677130307 10000000000 738904171087 1562500000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243139173/10000000000 : ℝ), (-354550323/2000000000 : ℝ), (5677130307/10000000000 : ℝ)] ![(4256795836643/10000000000000 : ℝ), (5071087333287/50000000000000 : ℝ), (738904171087/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243139173/10000000000 : ℝ)|^8393 ≤ (4256795836643/10000000000000 : ℝ)^6345
        have hw : |(5243139173/10000000000 : ℝ)|=(5243139173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354550323/2000000000 : ℝ)|^8393 ≤ (5071087333287/50000000000000 : ℝ)^6345
        have hw : |(-354550323/2000000000 : ℝ)|=(354550323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5677130307/10000000000 : ℝ)|^8393 ≤ (738904171087/1562500000000 : ℝ)^6345
        have hw : |(5677130307/10000000000 : ℝ)|=(5677130307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310784807/2500000000 : ℝ)*x 0 + (113542617/200000000 : ℝ)*x 1 + (-886375373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310784807/2500000000 : ℝ)^8393 ≤ (42567958957093/100000000000000 : ℝ)^6345 := by
    have hnat : (1310784807 : ℕ)^8393*100000000000000^6345 ≤ 42567958957093^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310784807 2500000000 42567958957093 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113542617/200000000 : ℝ)^8393 ≤ (23644936466323/50000000000000 : ℝ)^6345 := by
    have hnat : (113542617 : ℕ)^8393*50000000000000^6345 ≤ 23644936466323^6345*200000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113542617 200000000 23644936466323 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886375373/5000000000 : ℝ)^8393 ≤ (10142168090169/100000000000000 : ℝ)^6345 := by
    have hnat : (886375373 : ℕ)^8393*100000000000000^6345 ≤ 10142168090169^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886375373 5000000000 10142168090169 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310784807/2500000000 : ℝ), (113542617/200000000 : ℝ), (-886375373/5000000000 : ℝ)] ![(42567958957093/100000000000000 : ℝ), (23644936466323/50000000000000 : ℝ), (10142168090169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310784807/2500000000 : ℝ)|^8393 ≤ (42567958957093/100000000000000 : ℝ)^6345
        have hw : |(1310784807/2500000000 : ℝ)|=(1310784807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113542617/200000000 : ℝ)|^8393 ≤ (23644936466323/50000000000000 : ℝ)^6345
        have hw : |(113542617/200000000 : ℝ)|=(113542617/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-886375373/5000000000 : ℝ)|^8393 ≤ (10142168090169/100000000000000 : ℝ)^6345
        have hw : |(-886375373/5000000000 : ℝ)|=(886375373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s1_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4313951437/10000000000 : ℝ)*x 0 + (1255526413/2500000000 : ℝ)*x 1 + (3706226851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313951437/10000000000 : ℝ)^8393 ≤ (8221717388189/25000000000000 : ℝ)^6345 := by
    have hnat : (4313951437 : ℕ)^8393*25000000000000^6345 ≤ 8221717388189^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313951437 10000000000 8221717388189 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255526413/2500000000 : ℝ)^8393 ≤ (20105256840111/50000000000000 : ℝ)^6345 := by
    have hnat : (1255526413 : ℕ)^8393*50000000000000^6345 ≤ 20105256840111^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255526413 2500000000 20105256840111 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3706226851/10000000000 : ℝ)^8393 ≤ (13451308377239/50000000000000 : ℝ)^6345 := by
    have hnat : (3706226851 : ℕ)^8393*50000000000000^6345 ≤ 13451308377239^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3706226851 10000000000 13451308377239 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313951437/10000000000 : ℝ), (1255526413/2500000000 : ℝ), (3706226851/10000000000 : ℝ)] ![(8221717388189/25000000000000 : ℝ), (20105256840111/50000000000000 : ℝ), (13451308377239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313951437/10000000000 : ℝ)|^8393 ≤ (8221717388189/25000000000000 : ℝ)^6345
        have hw : |(4313951437/10000000000 : ℝ)|=(4313951437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255526413/2500000000 : ℝ)|^8393 ≤ (20105256840111/50000000000000 : ℝ)^6345
        have hw : |(1255526413/2500000000 : ℝ)|=(1255526413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3706226851/10000000000 : ℝ)|^8393 ≤ (13451308377239/50000000000000 : ℝ)^6345
        have hw : |(3706226851/10000000000 : ℝ)|=(3706226851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13797/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (373/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20179/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13797/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (13/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13797/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (13/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13797/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (13/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13797/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (13/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13797/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (13/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13797/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (13/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (13/2000 : ℝ) ^ (1049/256 : ℝ) ≤ (109161814653/100000000000000000000 : ℝ) := by
    have hpowers : (13/2000 : ℝ)^1049 ≤ (109161814653/100000000000000000000 : ℝ)^256 := by
      have hnat : (13 : ℕ)^1049*100000000000000000000^256 ≤ 109161814653^256*2000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 2000 109161814653 100000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/2000 : ℝ)) (X := (109161814653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13797/50000 : ℝ) ^ (1049/256 : ℝ) ≤ (127817613683120887/25000000000000000000 : ℝ) := by
    have hpowers : (13797/50000 : ℝ)^1049 ≤ (127817613683120887/25000000000000000000 : ℝ)^256 := by
      have hnat : (13797 : ℕ)^1049*25000000000000000000^256 ≤ 127817613683120887^256*50000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13797 50000 127817613683120887 25000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13797/50000 : ℝ)) (X := (127817613683120887/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000109161814653/50000000000000000000 : ℝ) ≤ (10000000005328013/10000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (50000000109161814653/50000000000000000000 : ℝ)^256 ≤ (10000000005328013/10000000000000000 : ℝ)^1049 := by
      have hnat : (50000000109161814653 : ℕ)^256*10000000000000000^1049 ≤ 10000000005328013^1049*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000109161814653 50000000000000000000 10000000005328013 10000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000005328013/10000000000000000 : ℝ)) (X := (50000000109161814653/50000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100511270563894298201/100000000000000000000 : ℝ) ≤ (1251556638267883/1250000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (100511270563894298201/100000000000000000000 : ℝ)^256 ≤ (1251556638267883/1250000000000000 : ℝ)^1049 := by
      have hnat : (100511270563894298201 : ℕ)^256*1250000000000000^1049 ≤ 1251556638267883^1049*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100511270563894298201 100000000000000000000 1251556638267883 1250000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251556638267883/1250000000000000 : ℝ)) (X := (100511270563894298201/100000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12627817613683120887/12500000000000000000 : ℝ) ≤ (2004981241391623/2000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (12627817613683120887/12500000000000000000 : ℝ)^256 ≤ (2004981241391623/2000000000000000 : ℝ)^1049 := by
      have hnat : (12627817613683120887 : ℕ)^256*2000000000000000^1049 ≤ 2004981241391623^1049*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12627817613683120887 12500000000000000000 2004981241391623 2000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004981241391623/2000000000000000 : ℝ)) (X := (12627817613683120887/12500000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109161814653/100000000000000000000 : ℝ) ≤ ((67355952778124603993/67360000000000000000 : ℝ)+2*(12453100815051/2694400000000000 : ℝ)*(13/2000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (67355952778124603993/67360000000000000000 : ℝ)+2*(12453100815051/2694400000000000 : ℝ)*(13/2000 : ℝ)=(10000000005328013/10000000000000000 : ℝ) by norm_num, show 1+2*(109161814653/100000000000000000000 : ℝ)=(50000000109161814653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(127817613683120887/25000000000000000000 : ℝ)+(109161814653/100000000000000000000 : ℝ) ≤ ((67355952778124603993/67360000000000000000 : ℝ)+(12453100815051/2694400000000000 : ℝ)*((13797/50000 : ℝ)+(13/2000 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (67355952778124603993/67360000000000000000 : ℝ)+(12453100815051/2694400000000000 : ℝ)*((13797/50000 : ℝ)+(13/2000 : ℝ))=(1251556638267883/1250000000000000 : ℝ) by norm_num, show 1+(127817613683120887/25000000000000000000 : ℝ)+(109161814653/100000000000000000000 : ℝ)=(100511270563894298201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(127817613683120887/25000000000000000000 : ℝ) ≤ ((67355952778124603993/67360000000000000000 : ℝ)+2*(12453100815051/2694400000000000 : ℝ)*(13797/50000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (67355952778124603993/67360000000000000000 : ℝ)+2*(12453100815051/2694400000000000 : ℝ)*(13797/50000 : ℝ)=(2004981241391623/2000000000000000 : ℝ) by norm_num, show 1+2*(127817613683120887/25000000000000000000 : ℝ)=(12627817613683120887/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67355952778124603993/67360000000000000000 : ℝ)*(X 1 0+X 2 0)+(12453100815051/2694400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (13/2000 : ℝ)) (hi := (13797/50000 : ℝ)) (c := (67355952778124603993/67360000000000000000 : ℝ)) (alpha := (12453100815051/2694400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67355952778124603993/67360000000000000000 : ℝ)*(X 0 1+X 2 1)+(12453100815051/2694400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (13/2000 : ℝ)) (hi := (13797/50000 : ℝ)) (c := (67355952778124603993/67360000000000000000 : ℝ)) (alpha := (12453100815051/2694400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67355952778124603993/67360000000000000000 : ℝ)*(X 0 2+X 1 2)+(12453100815051/2694400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (13/2000 : ℝ)) (hi := (13797/50000 : ℝ)) (c := (67355952778124603993/67360000000000000000 : ℝ)) (alpha := (12453100815051/2694400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-518513639/2500000000 : ℝ)*X 0 0+(2843139179/5000000000 : ℝ)*X 0 1+(2507091947/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415944461/10000000000 : ℝ)*X 1 0+(-1217848763/5000000000 : ℝ)*X 1 1+(156693259/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676992919/1250000000 : ℝ)*X 2 0+(1002837/2000000 : ℝ)*X 2 1+(-1217849031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312487121/10000000000 : ℝ)*X 0 0+(737563989/2000000000 : ℝ)*X 0 1+(5040163359/10000000000 : ℝ)*X 0 2+(4312487121/10000000000 : ℝ)*X 1 0+(737563989/2000000000 : ℝ)*X 1 1+(5040163359/10000000000 : ℝ)*X 1 2+(4312487121/10000000000 : ℝ)*X 2 0+(737563989/2000000000 : ℝ)*X 2 1+(5040163359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2074781697/10000000000 : ℝ)*X 0 0+(502315791/1000000000 : ℝ)*X 0 1+(5677131399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243139173/10000000000 : ℝ)*X 1 0+(-354550323/2000000000 : ℝ)*X 1 1+(5677130307/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1310784807/2500000000 : ℝ)*X 2 0+(113542617/200000000 : ℝ)*X 2 1+(-886375373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313951437/10000000000 : ℝ)*X 0 0+(1255526413/2500000000 : ℝ)*X 0 1+(3706226851/10000000000 : ℝ)*X 0 2+(4313951437/10000000000 : ℝ)*X 1 0+(1255526413/2500000000 : ℝ)*X 1 1+(3706226851/10000000000 : ℝ)*X 1 2+(4313951437/10000000000 : ℝ)*X 2 0+(1255526413/2500000000 : ℝ)*X 2 1+(3706226851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (806626820402409150038919/134720000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1546193189/100000000000000 : ℝ)*(base19) + (1190667867/100000000000000 : ℝ)*(base23) + (329452837/100000000000000 : ℝ)*(upper3) + (860689/3125000000000 : ℝ)*(upper4) + (11707713/100000000000000 : ℝ)*(upper5) + (1113685785116903/100000000000000 : ℝ)*(major0) + (1113685785116903/100000000000000 : ℝ)*(major1) + (1113685785116903/100000000000000 : ℝ)*(major2) + (743948545083079/50000000000000 : ℝ)*(sp0) + (185987885895627/12500000000000 : ℝ)*(sp1) + (1487903442690339/100000000000000 : ℝ)*(sp2) + (369730654099149/50000000000000 : ℝ)*(sp3) + (471449503/6250000000000 : ℝ)*(sp4) + (1357274059/25000000000000 : ℝ)*(sp7) + (369733368647267/50000000000000 : ℝ)*(f.failure) + (743952316679103/50000000000000 : ℝ)*(f.sum) + (3373799734867/134720000000000000000000000000 : ℝ)*base66 + (44250462859574081321/6736000000000000000000000000000000 : ℝ)*base68 + (2395781447369918679/6736000000000000000000000000000000 : ℝ)*base69 + (30573699818185918679/6736000000000000000000000000000000 : ℝ)*base71 + (787805138864467/134720000000000000000000000000 : ℝ)*base74 + (15361946889225918679/6736000000000000000000000000000000 : ℝ)*base75 + (9192275858486081321/6736000000000000000000000000000000 : ℝ)*base78 + (17569212367990081321/6736000000000000000000000000000000 : ℝ)*base80 + (287052489291053/134720000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1863487/500000000000000000000 : ℝ)*base89 + (1863487/500000000000000000000 : ℝ)*base91 + (1863487/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15501451516806449093648604993/3368000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57815353/100000000000000 : ℝ)*(base1) + (512837197/50000000000000 : ℝ)*(base19) + (1083695549/100000000000000 : ℝ)*(base23) + (36891573/100000000000000 : ℝ)*(base32) + (113784987/100000000000000 : ℝ)*(upper5) + (1144531625264333/100000000000000 : ℝ)*(major0) + (1144531625264333/100000000000000 : ℝ)*(major1) + (1144531625264333/100000000000000 : ℝ)*(major2) + (734852439/20000000000000 : ℝ)*(sp1) + (1237012801/25000000000000 : ℝ)*(sp2) + (1529115350997767/100000000000000 : ℝ)*(sp4) + (764555296622913/50000000000000 : ℝ)*(sp5) + (1529109261435661/100000000000000 : ℝ)*(sp6) + (759947709220361/100000000000000 : ℝ)*(sp7) + (379973901963643/50000000000000 : ℝ)*(f.failure) + (764557646591207/50000000000000 : ℝ)*(f.sum) + (2231712769777/134720000000000000000000000000 : ℝ)*base66 + (42410689729240143331/6736000000000000000000000000000000 : ℝ)*base68 + (18813272978887856669/6736000000000000000000000000000000 : ℝ)*base69 + (24363714709671856669/6736000000000000000000000000000000 : ℝ)*base71 + (850308077036657/134720000000000000000000000000 : ℝ)*base74 + (31253089140936143331/6736000000000000000000000000000000 : ℝ)*base76 + (6477534943543856669/6736000000000000000000000000000000 : ℝ)*base77 + (4851815159079856669/6736000000000000000000000000000000 : ℝ)*base79 + (10268474651057/134720000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3451977/500000000000000000000 : ℝ)*base90 + (3451977/500000000000000000000 : ℝ)*base92 + (3451977/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1200_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13797/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (373/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20179/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1200_s2_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062115789/5000000000 : ℝ)*x 0 + (2750055723/5000000000 : ℝ)*x 1 + (2584194827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062115789/5000000000 : ℝ)^8393 ≤ (12883688713939/100000000000000 : ℝ)^6345 := by
    have hnat : (1062115789 : ℕ)^8393*100000000000000^6345 ≤ 12883688713939^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062115789 5000000000 12883688713939 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750055723/5000000000 : ℝ)^8393 ≤ (2834328711101/6250000000000 : ℝ)^6345 := by
    have hnat : (2750055723 : ℕ)^8393*6250000000000^6345 ≤ 2834328711101^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750055723 5000000000 2834328711101 6250000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584194827/5000000000 : ℝ)^8393 ≤ (20883525949329/50000000000000 : ℝ)^6345 := by
    have hnat : (2584194827 : ℕ)^8393*50000000000000^6345 ≤ 20883525949329^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584194827 5000000000 20883525949329 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062115789/5000000000 : ℝ), (2750055723/5000000000 : ℝ), (2584194827/5000000000 : ℝ)] ![(12883688713939/100000000000000 : ℝ), (2834328711101/6250000000000 : ℝ), (20883525949329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062115789/5000000000 : ℝ)|^8393 ≤ (12883688713939/100000000000000 : ℝ)^6345
        have hw : |(-1062115789/5000000000 : ℝ)|=(1062115789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750055723/5000000000 : ℝ)|^8393 ≤ (2834328711101/6250000000000 : ℝ)^6345
        have hw : |(2750055723/5000000000 : ℝ)|=(2750055723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584194827/5000000000 : ℝ)|^8393 ≤ (20883525949329/50000000000000 : ℝ)^6345
        have hw : |(2584194827/5000000000 : ℝ)|=(2584194827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5371409169/10000000000 : ℝ)*x 0 + (-2296314517/10000000000 : ℝ)*x 1 + (5168394123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371409169/10000000000 : ℝ)^8393 ≤ (43950900769979/100000000000000 : ℝ)^6345 := by
    have hnat : (5371409169 : ℕ)^8393*100000000000000^6345 ≤ 43950900769979^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371409169 10000000000 43950900769979 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296314517/10000000000 : ℝ)^8393 ≤ (7140999773521/50000000000000 : ℝ)^6345 := by
    have hnat : (2296314517 : ℕ)^8393*50000000000000^6345 ≤ 7140999773521^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296314517 10000000000 7140999773521 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5168394123/10000000000 : ℝ)^8393 ≤ (8353419934157/20000000000000 : ℝ)^6345 := by
    have hnat : (5168394123 : ℕ)^8393*20000000000000^6345 ≤ 8353419934157^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168394123 10000000000 8353419934157 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371409169/10000000000 : ℝ), (-2296314517/10000000000 : ℝ), (5168394123/10000000000 : ℝ)] ![(43950900769979/100000000000000 : ℝ), (7140999773521/50000000000000 : ℝ), (8353419934157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371409169/10000000000 : ℝ)|^8393 ≤ (43950900769979/100000000000000 : ℝ)^6345
        have hw : |(5371409169/10000000000 : ℝ)|=(5371409169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2296314517/10000000000 : ℝ)|^8393 ≤ (7140999773521/50000000000000 : ℝ)^6345
        have hw : |(-2296314517/10000000000 : ℝ)|=(2296314517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5168394123/10000000000 : ℝ)|^8393 ≤ (8353419934157/20000000000000 : ℝ)^6345
        have hw : |(5168394123/10000000000 : ℝ)|=(5168394123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53714111/100000000 : ℝ)*x 0 + (1292097857/2500000000 : ℝ)*x 1 + (-2296315477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53714111/100000000 : ℝ)^8393 ≤ (8790184334007/20000000000000 : ℝ)^6345 := by
    have hnat : (53714111 : ℕ)^8393*20000000000000^6345 ≤ 8790184334007^6345*100000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53714111 100000000 8790184334007 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292097857/2500000000 : ℝ)^8393 ≤ (2610441928883/6250000000000 : ℝ)^6345 := by
    have hnat : (1292097857 : ℕ)^8393*6250000000000^6345 ≤ 2610441928883^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292097857 2500000000 2610441928883 6250000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296315477/10000000000 : ℝ)^8393 ≤ (7141003722497/50000000000000 : ℝ)^6345 := by
    have hnat : (2296315477 : ℕ)^8393*50000000000000^6345 ≤ 7141003722497^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296315477 10000000000 7141003722497 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53714111/100000000 : ℝ), (1292097857/2500000000 : ℝ), (-2296315477/10000000000 : ℝ)] ![(8790184334007/20000000000000 : ℝ), (2610441928883/6250000000000 : ℝ), (7141003722497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53714111/100000000 : ℝ)|^8393 ≤ (8790184334007/20000000000000 : ℝ)^6345
        have hw : |(53714111/100000000 : ℝ)|=(53714111/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292097857/2500000000 : ℝ)|^8393 ≤ (2610441928883/6250000000000 : ℝ)^6345
        have hw : |(1292097857/2500000000 : ℝ)|=(1292097857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2296315477/10000000000 : ℝ)|^8393 ≤ (7141003722497/50000000000000 : ℝ)^6345
        have hw : |(-2296315477/10000000000 : ℝ)|=(2296315477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1086762293/2500000000 : ℝ)*x 0 + (4025844619/10000000000 : ℝ)*x 1 + (938661771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086762293/2500000000 : ℝ)^8393 ≤ (33221039691647/100000000000000 : ℝ)^6345 := by
    have hnat : (1086762293 : ℕ)^8393*100000000000000^6345 ≤ 33221039691647^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086762293 2500000000 33221039691647 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025844619/10000000000 : ℝ)^8393 ≤ (30013399513307/100000000000000 : ℝ)^6345 := by
    have hnat : (4025844619 : ℕ)^8393*100000000000000^6345 ≤ 30013399513307^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025844619 10000000000 30013399513307 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (938661771/2000000000 : ℝ)^8393 ≤ (36765560784291/100000000000000 : ℝ)^6345 := by
    have hnat : (938661771 : ℕ)^8393*100000000000000^6345 ≤ 36765560784291^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938661771 2000000000 36765560784291 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086762293/2500000000 : ℝ), (4025844619/10000000000 : ℝ), (938661771/2000000000 : ℝ)] ![(33221039691647/100000000000000 : ℝ), (30013399513307/100000000000000 : ℝ), (36765560784291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086762293/2500000000 : ℝ)|^8393 ≤ (33221039691647/100000000000000 : ℝ)^6345
        have hw : |(1086762293/2500000000 : ℝ)|=(1086762293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025844619/10000000000 : ℝ)|^8393 ≤ (30013399513307/100000000000000 : ℝ)^6345
        have hw : |(4025844619/10000000000 : ℝ)|=(4025844619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(938661771/2000000000 : ℝ)|^8393 ≤ (36765560784291/100000000000000 : ℝ)^6345
        have hw : |(938661771/2000000000 : ℝ)|=(938661771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-265539767/1250000000 : ℝ)*x 0 + (5170587129/10000000000 : ℝ)*x 1 + (5497893689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265539767/1250000000 : ℝ)^8393 ≤ (644219157641/5000000000000 : ℝ)^6345 := by
    have hnat : (265539767 : ℕ)^8393*5000000000000^6345 ≤ 644219157641^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265539767 1250000000 644219157641 5000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5170587129/10000000000 : ℝ)^8393 ≤ (20895271893003/50000000000000 : ℝ)^6345 := by
    have hnat : (5170587129 : ℕ)^8393*50000000000000^6345 ≤ 20895271893003^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170587129 10000000000 20895271893003 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497893689/10000000000 : ℝ)^8393 ≤ (2832817065387/6250000000000 : ℝ)^6345 := by
    have hnat : (5497893689 : ℕ)^8393*6250000000000^6345 ≤ 2832817065387^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497893689 10000000000 2832817065387 6250000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265539767/1250000000 : ℝ), (5170587129/10000000000 : ℝ), (5497893689/10000000000 : ℝ)] ![(644219157641/5000000000000 : ℝ), (20895271893003/50000000000000 : ℝ), (2832817065387/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265539767/1250000000 : ℝ)|^8393 ≤ (644219157641/5000000000000 : ℝ)^6345
        have hw : |(-265539767/1250000000 : ℝ)|=(265539767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5170587129/10000000000 : ℝ)|^8393 ≤ (20895271893003/50000000000000 : ℝ)^6345
        have hw : |(5170587129/10000000000 : ℝ)|=(5170587129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497893689/10000000000 : ℝ)|^8393 ≤ (2832817065387/6250000000000 : ℝ)^6345
        have hw : |(5497893689/10000000000 : ℝ)|=(5497893689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1321730817/2500000000 : ℝ)*x 0 + (-1966813277/10000000000 : ℝ)*x 1 + (5497893709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321730817/2500000000 : ℝ)^8393 ≤ (43038802556969/100000000000000 : ℝ)^6345 := by
    have hnat : (1321730817 : ℕ)^8393*100000000000000^6345 ≤ 43038802556969^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321730817 2500000000 43038802556969 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966813277/10000000000 : ℝ)^8393 ≤ (5818062084309/50000000000000 : ℝ)^6345 := by
    have hnat : (1966813277 : ℕ)^8393*50000000000000^6345 ≤ 5818062084309^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966813277 10000000000 5818062084309 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5497893709/10000000000 : ℝ)^8393 ≤ (45325073264293/100000000000000 : ℝ)^6345 := by
    have hnat : (5497893709 : ℕ)^8393*100000000000000^6345 ≤ 45325073264293^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497893709 10000000000 45325073264293 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321730817/2500000000 : ℝ), (-1966813277/10000000000 : ℝ), (5497893709/10000000000 : ℝ)] ![(43038802556969/100000000000000 : ℝ), (5818062084309/50000000000000 : ℝ), (45325073264293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321730817/2500000000 : ℝ)|^8393 ≤ (43038802556969/100000000000000 : ℝ)^6345
        have hw : |(1321730817/2500000000 : ℝ)|=(1321730817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1966813277/10000000000 : ℝ)|^8393 ≤ (5818062084309/50000000000000 : ℝ)^6345
        have hw : |(-1966813277/10000000000 : ℝ)|=(1966813277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5497893709/10000000000 : ℝ)|^8393 ≤ (45325073264293/100000000000000 : ℝ)^6345
        have hw : |(5497893709/10000000000 : ℝ)|=(5497893709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66086543/125000000 : ℝ)*x 0 + (171809179/312500000 : ℝ)*x 1 + (-1966813013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66086543/125000000 : ℝ)^8393 ≤ (43038804409097/100000000000000 : ℝ)^6345 := by
    have hnat : (66086543 : ℕ)^8393*100000000000000^6345 ≤ 43038804409097^6345*125000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66086543 125000000 43038804409097 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171809179/312500000 : ℝ)^8393 ≤ (45325073471489/100000000000000 : ℝ)^6345 := by
    have hnat : (171809179 : ℕ)^8393*100000000000000^6345 ≤ 45325073471489^6345*312500000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171809179 312500000 45325073471489 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966813013/10000000000 : ℝ)^8393 ≤ (11636122102597/100000000000000 : ℝ)^6345 := by
    have hnat : (1966813013 : ℕ)^8393*100000000000000^6345 ≤ 11636122102597^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966813013 10000000000 11636122102597 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66086543/125000000 : ℝ), (171809179/312500000 : ℝ), (-1966813013/10000000000 : ℝ)] ![(43038804409097/100000000000000 : ℝ), (45325073471489/100000000000000 : ℝ), (11636122102597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66086543/125000000 : ℝ)|^8393 ≤ (43038804409097/100000000000000 : ℝ)^6345
        have hw : |(66086543/125000000 : ℝ)|=(66086543/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171809179/312500000 : ℝ)|^8393 ≤ (45325073471489/100000000000000 : ℝ)^6345
        have hw : |(171809179/312500000 : ℝ)|=(171809179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966813013/10000000000 : ℝ)|^8393 ≤ (11636122102597/100000000000000 : ℝ)^6345
        have hw : |(-1966813013/10000000000 : ℝ)|=(1966813013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s2_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4347225697/10000000000 : ℝ)*x 0 + (4688889983/10000000000 : ℝ)*x 1 + (2015152669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347225697/10000000000 : ℝ)^8393 ≤ (4152853022301/12500000000000 : ℝ)^6345 := by
    have hnat : (4347225697 : ℕ)^8393*12500000000000^6345 ≤ 4152853022301^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347225697 10000000000 4152853022301 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4688889983/10000000000 : ℝ)^8393 ≤ (9179944740693/25000000000000 : ℝ)^6345 := by
    have hnat : (4688889983 : ℕ)^8393*25000000000000^6345 ≤ 9179944740693^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4688889983 10000000000 9179944740693 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015152669/5000000000 : ℝ)^8393 ≤ (30057396838781/100000000000000 : ℝ)^6345 := by
    have hnat : (2015152669 : ℕ)^8393*100000000000000^6345 ≤ 30057396838781^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015152669 5000000000 30057396838781 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347225697/10000000000 : ℝ), (4688889983/10000000000 : ℝ), (2015152669/5000000000 : ℝ)] ![(4152853022301/12500000000000 : ℝ), (9179944740693/25000000000000 : ℝ), (30057396838781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347225697/10000000000 : ℝ)|^8393 ≤ (4152853022301/12500000000000 : ℝ)^6345
        have hw : |(4347225697/10000000000 : ℝ)|=(4347225697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4688889983/10000000000 : ℝ)|^8393 ≤ (9179944740693/25000000000000 : ℝ)^6345
        have hw : |(4688889983/10000000000 : ℝ)|=(4688889983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015152669/5000000000 : ℝ)|^8393 ≤ (30057396838781/100000000000000 : ℝ)^6345
        have hw : |(2015152669/5000000000 : ℝ)|=(2015152669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (373/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1021/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (373/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (373/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (373/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (373/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (373/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (373/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (373/6250 : ℝ) ^ (1049/256 : ℝ) ≤ (963312710204417/100000000000000000000 : ℝ) := by
    have hpowers : (373/6250 : ℝ)^1049 ≤ (963312710204417/100000000000000000000 : ℝ)^256 := by
      have hnat : (373 : ℕ)^1049*100000000000000000000^256 ≤ 963312710204417^256*6250^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        373 6250 963312710204417 100000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (373/6250 : ℝ)) (X := (963312710204417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (20179/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (35453382441705971/25000000000000000000 : ℝ) := by
    have hpowers : (20179/100000 : ℝ)^1049 ≤ (35453382441705971/25000000000000000000 : ℝ)^256 := by
      have hnat : (20179 : ℕ)^1049*25000000000000000000^256 ≤ 35453382441705971^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20179 100000 35453382441705971 25000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20179/100000 : ℝ)) (X := (35453382441705971/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000963312710204417/50000000000000000000 : ℝ) ≤ (5000023508699521/5000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (50000963312710204417/50000000000000000000 : ℝ)^256 ≤ (5000023508699521/5000000000000000 : ℝ)^1049 := by
      have hnat : (50000963312710204417 : ℕ)^256*5000000000000000^1049 ≤ 5000023508699521^1049*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000963312710204417 50000000000000000000 5000023508699521 5000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000023508699521/5000000000000000 : ℝ)) (X := (50000963312710204417/50000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100142776842477028301/100000000000000000000 : ℝ) ≤ (10003482475010543/10000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (100142776842477028301/100000000000000000000 : ℝ)^256 ≤ (10003482475010543/10000000000000000 : ℝ)^1049 := by
      have hnat : (100142776842477028301 : ℕ)^256*10000000000000000^1049 ≤ 10003482475010543^1049*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100142776842477028301 100000000000000000000 10003482475010543 10000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003482475010543/10000000000000000 : ℝ)) (X := (100142776842477028301/100000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12535453382441705971/12500000000000000000 : ℝ) ≤ (2501729483155511/2500000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (12535453382441705971/12500000000000000000 : ℝ)^256 ≤ (2501729483155511/2500000000000000 : ℝ)^1049 := by
      have hnat : (12535453382441705971 : ℕ)^256*2500000000000000^1049 ≤ 2501729483155511^1049*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12535453382441705971 12500000000000000000 2501729483155511 2500000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501729483155511/2500000000000000 : ℝ)) (X := (12535453382441705971/12500000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(963312710204417/100000000000000000000 : ℝ) ≤ ((7892759030122606107/7895000000000000000 : ℝ)+2*(381717512389/157900000000000 : ℝ)*(373/6250 : ℝ))^(1049/256 : ℝ) := by
    rw [show (7892759030122606107/7895000000000000000 : ℝ)+2*(381717512389/157900000000000 : ℝ)*(373/6250 : ℝ)=(5000023508699521/5000000000000000 : ℝ) by norm_num, show 1+2*(963312710204417/100000000000000000000 : ℝ)=(50000963312710204417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35453382441705971/25000000000000000000 : ℝ)+(963312710204417/100000000000000000000 : ℝ) ≤ ((7892759030122606107/7895000000000000000 : ℝ)+(381717512389/157900000000000 : ℝ)*((20179/100000 : ℝ)+(373/6250 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (7892759030122606107/7895000000000000000 : ℝ)+(381717512389/157900000000000 : ℝ)*((20179/100000 : ℝ)+(373/6250 : ℝ))=(10003482475010543/10000000000000000 : ℝ) by norm_num, show 1+(35453382441705971/25000000000000000000 : ℝ)+(963312710204417/100000000000000000000 : ℝ)=(100142776842477028301/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35453382441705971/25000000000000000000 : ℝ) ≤ ((7892759030122606107/7895000000000000000 : ℝ)+2*(381717512389/157900000000000 : ℝ)*(20179/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (7892759030122606107/7895000000000000000 : ℝ)+2*(381717512389/157900000000000 : ℝ)*(20179/100000 : ℝ)=(2501729483155511/2500000000000000 : ℝ) by norm_num, show 1+2*(35453382441705971/25000000000000000000 : ℝ)=(12535453382441705971/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7892759030122606107/7895000000000000000 : ℝ)*(X 1 0+X 2 0)+(381717512389/157900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (373/6250 : ℝ)) (hi := (20179/100000 : ℝ)) (c := (7892759030122606107/7895000000000000000 : ℝ)) (alpha := (381717512389/157900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7892759030122606107/7895000000000000000 : ℝ)*(X 0 1+X 2 1)+(381717512389/157900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (373/6250 : ℝ)) (hi := (20179/100000 : ℝ)) (c := (7892759030122606107/7895000000000000000 : ℝ)) (alpha := (381717512389/157900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7892759030122606107/7895000000000000000 : ℝ)*(X 0 2+X 1 2)+(381717512389/157900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (373/6250 : ℝ)) (hi := (20179/100000 : ℝ)) (c := (7892759030122606107/7895000000000000000 : ℝ)) (alpha := (381717512389/157900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1062115789/5000000000 : ℝ)*X 0 0+(2750055723/5000000000 : ℝ)*X 0 1+(2584194827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371409169/10000000000 : ℝ)*X 1 0+(-2296314517/10000000000 : ℝ)*X 1 1+(5168394123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53714111/100000000 : ℝ)*X 2 0+(1292097857/2500000000 : ℝ)*X 2 1+(-2296315477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086762293/2500000000 : ℝ)*X 0 0+(4025844619/10000000000 : ℝ)*X 0 1+(938661771/2000000000 : ℝ)*X 0 2+(1086762293/2500000000 : ℝ)*X 1 0+(4025844619/10000000000 : ℝ)*X 1 1+(938661771/2000000000 : ℝ)*X 1 2+(1086762293/2500000000 : ℝ)*X 2 0+(4025844619/10000000000 : ℝ)*X 2 1+(938661771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-265539767/1250000000 : ℝ)*X 0 0+(5170587129/10000000000 : ℝ)*X 0 1+(5497893689/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1321730817/2500000000 : ℝ)*X 1 0+(-1966813277/10000000000 : ℝ)*X 1 1+(5497893709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66086543/125000000 : ℝ)*X 2 0+(171809179/312500000 : ℝ)*X 2 1+(-1966813013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347225697/10000000000 : ℝ)*X 0 0+(4688889983/10000000000 : ℝ)*X 0 1+(2015152669/5000000000 : ℝ)*X 0 2+(4347225697/10000000000 : ℝ)*X 1 0+(4688889983/10000000000 : ℝ)*X 1 1+(2015152669/5000000000 : ℝ)*X 1 2+(4347225697/10000000000 : ℝ)*X 2 0+(4688889983/10000000000 : ℝ)*X 2 1+(2015152669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18101394447217697192159037/6167968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (248305761/100000000000000 : ℝ)*(base19) + (1249602601/100000000000000 : ℝ)*(base23) + (352601/200000000000 : ℝ)*(upper2) + (475058509/100000000000000 : ℝ)*(upper3) + (220589463/100000000000000 : ℝ)*(upper4) + (141027174340121/6250000000000 : ℝ)*(major0) + (141027174340121/6250000000000 : ℝ)*(major1) + (141027174340121/6250000000000 : ℝ)*(major2) + (3014608456571531/100000000000000 : ℝ)*(sp0) + (3014638318823419/100000000000000 : ℝ)*(sp1) + (1507318658763289/50000000000000 : ℝ)*(sp2) + (749108025812231/50000000000000 : ℝ)*(sp3) + (30110557649/100000000000000 : ℝ)*(sp4) + (14862305503/100000000000000 : ℝ)*(sp7) + (374557728482491/25000000000000 : ℝ)*(f.failure) + (150731928356459/5000000000000 : ℝ)*(f.sum) + (6204285587769/7895000000000000000000000000 : ℝ)*base65 + (524123722296393553/49343750000000000000000000000000 : ℝ)*base68 + (658472615821862303/49343750000000000000000000000000 : ℝ)*base70 + (332230560873518553/49343750000000000000000000000000 : ℝ)*base72 + (4284803910619/1973750000000000000000000000 : ℝ)*base74 + (618763188698674803/49343750000000000000000000000000 : ℝ)*base76 + (209151803236987303/49343750000000000000000000000000 : ℝ)*base78 + (99502488315862303/49343750000000000000000000000000 : ℝ)*base80 + (14498616687753/3947500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1386551/250000000000000000000 : ℝ)*base89 + (1386551/250000000000000000000 : ℝ)*base91 + (1386551/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (693014445856420273772256363/98687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1728952121/100000000000000 : ℝ)*(base19) + (1922955853/100000000000000 : ℝ)*(base23) + (15400091/100000000000000 : ℝ)*(upper2) + (221684013/100000000000000 : ℝ)*(upper3) + (14507511/10000000000000 : ℝ)*(upper5) + (1143411876849097/50000000000000 : ℝ)*(major0) + (1143411876849097/50000000000000 : ℝ)*(major1) + (1143411876849097/50000000000000 : ℝ)*(major2) + (8540512803/50000000000000 : ℝ)*(sp1) + (1323630473/6250000000000 : ℝ)*(sp2) + (1527619324943787/50000000000000 : ℝ)*(sp4) + (1527609919954923/50000000000000 : ℝ)*(sp5) + (3055215548844153/100000000000000 : ℝ)*(sp6) + (151840862343173/10000000000000 : ℝ)*(sp7) + (151840862343173/10000000000000 : ℝ)*(f.failure) + (1527619324943787/50000000000000 : ℝ)*(f.sum) + (11257394012301/1973750000000000000000000000 : ℝ)*base66 + (2685021012035285379/394750000000000000000000000000000 : ℝ)*base67 + (2431789048882785379/394750000000000000000000000000000 : ℝ)*base69 + (3880383889294285379/394750000000000000000000000000000 : ℝ)*base71 + (8902886320801/1973750000000000000000000000 : ℝ)*base74 + (5329509899779285379/394750000000000000000000000000000 : ℝ)*base75 + (500540943771214621/394750000000000000000000000000000 : ℝ)*base78 + (3912178583555785379/394750000000000000000000000000000 : ℝ)*base79 + (7422517803959/7895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (217353/100000000000000000000 : ℝ)*base89 + (217353/100000000000000000000 : ℝ)*base91 + (217353/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1200_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1200_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1200_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1200_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1200_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1200_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
