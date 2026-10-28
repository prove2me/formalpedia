-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:35:24.608221+00:00
-- url     : https://prove2.me/submissions/bc2b52ad-6678-4784-a08c-31d171b1d901

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
theorem support_rectangle_w1150_box_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018218537/5000000000 : ℝ)*x 0 + (1075239213/2000000000 : ℝ)*x 1 + (1344049117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018218537/5000000000 : ℝ)^8343 ≤ (303361716387/2500000000000 : ℝ)^6295 := by
    have hnat : (1018218537 : ℕ)^8343*2500000000000^6295 ≤ 303361716387^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018218537 5000000000 303361716387 2500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075239213/2000000000 : ℝ)^8343 ≤ (5491595435163/12500000000000 : ℝ)^6295 := by
    have hnat : (1075239213 : ℕ)^8343*12500000000000^6295 ≤ 5491595435163^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075239213 2000000000 5491595435163 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344049117/2500000000 : ℝ)^8343 ≤ (43932767845909/100000000000000 : ℝ)^6295 := by
    have hnat : (1344049117 : ℕ)^8343*100000000000000^6295 ≤ 43932767845909^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344049117 2500000000 43932767845909 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018218537/5000000000 : ℝ), (1075239213/2000000000 : ℝ), (1344049117/2500000000 : ℝ)] ![(303361716387/2500000000000 : ℝ), (5491595435163/12500000000000 : ℝ), (43932767845909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018218537/5000000000 : ℝ)|^8343 ≤ (303361716387/2500000000000 : ℝ)^6295
        have hw : |(-1018218537/5000000000 : ℝ)|=(1018218537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075239213/2000000000 : ℝ)|^8343 ≤ (5491595435163/12500000000000 : ℝ)^6295
        have hw : |(1075239213/2000000000 : ℝ)|=(1075239213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344049117/2500000000 : ℝ)|^8343 ≤ (43932767845909/100000000000000 : ℝ)^6295
        have hw : |(1344049117/2500000000 : ℝ)|=(1344049117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296056753/10000000000 : ℝ)*x 0 + (-536284833/2500000000 : ℝ)*x 1 + (5376196831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296056753/10000000000 : ℝ)^8343 ≤ (1722677738079/4000000000000 : ℝ)^6295 := by
    have hnat : (5296056753 : ℕ)^8343*4000000000000^6295 ≤ 1722677738079^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296056753 10000000000 1722677738079 4000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536284833/2500000000 : ℝ)^8343 ≤ (13000284755587/100000000000000 : ℝ)^6295 := by
    have hnat : (536284833 : ℕ)^8343*100000000000000^6295 ≤ 13000284755587^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536284833 2500000000 13000284755587 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376196831/10000000000 : ℝ)^8343 ≤ (43932771777303/100000000000000 : ℝ)^6295 := by
    have hnat : (5376196831 : ℕ)^8343*100000000000000^6295 ≤ 43932771777303^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376196831 10000000000 43932771777303 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296056753/10000000000 : ℝ), (-536284833/2500000000 : ℝ), (5376196831/10000000000 : ℝ)] ![(1722677738079/4000000000000 : ℝ), (13000284755587/100000000000000 : ℝ), (43932771777303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296056753/10000000000 : ℝ)|^8343 ≤ (1722677738079/4000000000000 : ℝ)^6295
        have hw : |(5296056753/10000000000 : ℝ)|=(5296056753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-536284833/2500000000 : ℝ)|^8343 ≤ (13000284755587/100000000000000 : ℝ)^6295
        have hw : |(-536284833/2500000000 : ℝ)|=(536284833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376196831/10000000000 : ℝ)|^8343 ≤ (43932771777303/100000000000000 : ℝ)^6295
        have hw : |(5376196831/10000000000 : ℝ)|=(5376196831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (662007201/1250000000 : ℝ)*x 0 + (5376196289/10000000000 : ℝ)*x 1 + (-429027783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662007201/1250000000 : ℝ)^8343 ≤ (2691684541671/6250000000000 : ℝ)^6295 := by
    have hnat : (662007201 : ℕ)^8343*6250000000000^6295 ≤ 2691684541671^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662007201 1250000000 2691684541671 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376196289/10000000000 : ℝ)^8343 ≤ (5491595738411/12500000000000 : ℝ)^6295 := by
    have hnat : (5376196289 : ℕ)^8343*12500000000000^6295 ≤ 5491595738411^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376196289 10000000000 5491595738411 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429027783/2000000000 : ℝ)^8343 ≤ (6500140703121/50000000000000 : ℝ)^6295 := by
    have hnat : (429027783 : ℕ)^8343*50000000000000^6295 ≤ 6500140703121^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429027783 2000000000 6500140703121 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662007201/1250000000 : ℝ), (5376196289/10000000000 : ℝ), (-429027783/2000000000 : ℝ)] ![(2691684541671/6250000000000 : ℝ), (5491595738411/12500000000000 : ℝ), (6500140703121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662007201/1250000000 : ℝ)|^8343 ≤ (2691684541671/6250000000000 : ℝ)^6295
        have hw : |(662007201/1250000000 : ℝ)|=(662007201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376196289/10000000000 : ℝ)|^8343 ≤ (5491595738411/12500000000000 : ℝ)^6295
        have hw : |(5376196289/10000000000 : ℝ)|=(5376196289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429027783/2000000000 : ℝ)|^8343 ≤ (6500140703121/50000000000000 : ℝ)^6295
        have hw : |(-429027783/2000000000 : ℝ)|=(429027783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2235506027/5000000000 : ℝ)*x 0 + (2155960509/5000000000 : ℝ)*x 1 + (2155960461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2235506027/5000000000 : ℝ)^8343 ≤ (688176316451/2000000000000 : ℝ)^6295 := by
    have hnat : (2235506027 : ℕ)^8343*2000000000000^6295 ≤ 688176316451^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235506027 5000000000 688176316451 2000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155960509/5000000000 : ℝ)^8343 ≤ (16397796282373/50000000000000 : ℝ)^6295 := by
    have hnat : (2155960509 : ℕ)^8343*50000000000000^6295 ≤ 16397796282373^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155960509 5000000000 16397796282373 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155960461/5000000000 : ℝ)^8343 ≤ (16397795798521/50000000000000 : ℝ)^6295 := by
    have hnat : (2155960461 : ℕ)^8343*50000000000000^6295 ≤ 16397795798521^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155960461 5000000000 16397795798521 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2235506027/5000000000 : ℝ), (2155960509/5000000000 : ℝ), (2155960461/5000000000 : ℝ)] ![(688176316451/2000000000000 : ℝ), (16397796282373/50000000000000 : ℝ), (16397795798521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2235506027/5000000000 : ℝ)|^8343 ≤ (688176316451/2000000000000 : ℝ)^6295
        have hw : |(2235506027/5000000000 : ℝ)|=(2235506027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2155960509/5000000000 : ℝ)|^8343 ≤ (16397796282373/50000000000000 : ℝ)^6295
        have hw : |(2155960509/5000000000 : ℝ)|=(2155960509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2155960461/5000000000 : ℝ)|^8343 ≤ (16397795798521/50000000000000 : ℝ)^6295
        have hw : |(2155960461/5000000000 : ℝ)|=(2155960461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2291088451/10000000000 : ℝ)*x 0 + (330077513/625000000 : ℝ)*x 1 + (5281241013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2291088451/10000000000 : ℝ)^8343 ≤ (7092664764231/50000000000000 : ℝ)^6295 := by
    have hnat : (2291088451 : ℕ)^8343*50000000000000^6295 ≤ 7092664764231^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291088451 10000000000 7092664764231 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330077513/625000000 : ℝ)^8343 ≤ (10726832723287/25000000000000 : ℝ)^6295 := by
    have hnat : (330077513 : ℕ)^8343*25000000000000^6295 ≤ 10726832723287^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330077513 625000000 10726832723287 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281241013/10000000000 : ℝ)^8343 ≤ (42907339561129/100000000000000 : ℝ)^6295 := by
    have hnat : (5281241013 : ℕ)^8343*100000000000000^6295 ≤ 42907339561129^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281241013 10000000000 42907339561129 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2291088451/10000000000 : ℝ), (330077513/625000000 : ℝ), (5281241013/10000000000 : ℝ)] ![(7092664764231/50000000000000 : ℝ), (10726832723287/25000000000000 : ℝ), (42907339561129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2291088451/10000000000 : ℝ)|^8343 ≤ (7092664764231/50000000000000 : ℝ)^6295
        have hw : |(-2291088451/10000000000 : ℝ)|=(2291088451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330077513/625000000 : ℝ)|^8343 ≤ (10726832723287/25000000000000 : ℝ)^6295
        have hw : |(330077513/625000000 : ℝ)|=(330077513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281241013/10000000000 : ℝ)|^8343 ≤ (42907339561129/100000000000000 : ℝ)^6295
        have hw : |(5281241013/10000000000 : ℝ)|=(5281241013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363131351/10000000000 : ℝ)*x 0 + (-1091258249/5000000000 : ℝ)*x 1 + (660155007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363131351/10000000000 : ℝ)^8343 ≤ (43791324853447/100000000000000 : ℝ)^6295 := by
    have hnat : (5363131351 : ℕ)^8343*100000000000000^6295 ≤ 43791324853447^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363131351 10000000000 43791324853447 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091258249/5000000000 : ℝ)^8343 ≤ (6650672936273/50000000000000 : ℝ)^6295 := by
    have hnat : (1091258249 : ℕ)^8343*50000000000000^6295 ≤ 6650672936273^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091258249 5000000000 6650672936273 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660155007/1250000000 : ℝ)^8343 ≤ (42907329256461/100000000000000 : ℝ)^6295 := by
    have hnat : (660155007 : ℕ)^8343*100000000000000^6295 ≤ 42907329256461^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660155007 1250000000 42907329256461 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363131351/10000000000 : ℝ), (-1091258249/5000000000 : ℝ), (660155007/1250000000 : ℝ)] ![(43791324853447/100000000000000 : ℝ), (6650672936273/50000000000000 : ℝ), (42907329256461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363131351/10000000000 : ℝ)|^8343 ≤ (43791324853447/100000000000000 : ℝ)^6295
        have hw : |(5363131351/10000000000 : ℝ)|=(5363131351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091258249/5000000000 : ℝ)|^8343 ≤ (6650672936273/50000000000000 : ℝ)^6295
        have hw : |(-1091258249/5000000000 : ℝ)|=(1091258249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660155007/1250000000 : ℝ)|^8343 ≤ (42907329256461/100000000000000 : ℝ)^6295
        have hw : |(660155007/1250000000 : ℝ)|=(660155007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363131349/10000000000 : ℝ)*x 0 + (5281239917/10000000000 : ℝ)*x 1 + (-2182516687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363131349/10000000000 : ℝ)^8343 ≤ (10947831207951/25000000000000 : ℝ)^6295 := by
    have hnat : (5363131349 : ℕ)^8343*25000000000000^6295 ≤ 10947831207951^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363131349 10000000000 10947831207951 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281239917/10000000000 : ℝ)^8343 ≤ (42907327759753/100000000000000 : ℝ)^6295 := by
    have hnat : (5281239917 : ℕ)^8343*100000000000000^6295 ≤ 42907327759753^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281239917 10000000000 42907327759753 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182516687/10000000000 : ℝ)^8343 ≤ (13301347399149/100000000000000 : ℝ)^6295 := by
    have hnat : (2182516687 : ℕ)^8343*100000000000000^6295 ≤ 13301347399149^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182516687 10000000000 13301347399149 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363131349/10000000000 : ℝ), (5281239917/10000000000 : ℝ), (-2182516687/10000000000 : ℝ)] ![(10947831207951/25000000000000 : ℝ), (42907327759753/100000000000000 : ℝ), (13301347399149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363131349/10000000000 : ℝ)|^8343 ≤ (10947831207951/25000000000000 : ℝ)^6295
        have hw : |(5363131349/10000000000 : ℝ)|=(5363131349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281239917/10000000000 : ℝ)|^8343 ≤ (42907327759753/100000000000000 : ℝ)^6295
        have hw : |(5281239917/10000000000 : ℝ)|=(5281239917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182516687/10000000000 : ℝ)|^8343 ≤ (13301347399149/100000000000000 : ℝ)^6295
        have hw : |(-2182516687/10000000000 : ℝ)|=(2182516687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2127861477/5000000000 : ℝ)*x 0 + (2209772953/5000000000 : ℝ)*x 1 + (4419543583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127861477/5000000000 : ℝ)^8343 ≤ (32230306723651/100000000000000 : ℝ)^6295 := by
    have hnat : (2127861477 : ℕ)^8343*100000000000000^6295 ≤ 32230306723651^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127861477 5000000000 32230306723651 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209772953/5000000000 : ℝ)^8343 ≤ (33884858438877/100000000000000 : ℝ)^6295 := by
    have hnat : (2209772953 : ℕ)^8343*100000000000000^6295 ≤ 33884858438877^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209772953 5000000000 33884858438877 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419543583/10000000000 : ℝ)^8343 ≤ (33884834833893/100000000000000 : ℝ)^6295 := by
    have hnat : (4419543583 : ℕ)^8343*100000000000000^6295 ≤ 33884834833893^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419543583 10000000000 33884834833893 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127861477/5000000000 : ℝ), (2209772953/5000000000 : ℝ), (4419543583/10000000000 : ℝ)] ![(32230306723651/100000000000000 : ℝ), (33884858438877/100000000000000 : ℝ), (33884834833893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127861477/5000000000 : ℝ)|^8343 ≤ (32230306723651/100000000000000 : ℝ)^6295
        have hw : |(2127861477/5000000000 : ℝ)|=(2127861477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209772953/5000000000 : ℝ)|^8343 ≤ (33884858438877/100000000000000 : ℝ)^6295
        have hw : |(2209772953/5000000000 : ℝ)|=(2209772953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4419543583/10000000000 : ℝ)|^8343 ≤ (33884834833893/100000000000000 : ℝ)^6295
        have hw : |(4419543583/10000000000 : ℝ)|=(4419543583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_8 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-55945697/250000000 : ℝ)*x 0 + (5216645629/10000000000 : ℝ)*x 1 + (1346451519/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55945697/250000000 : ℝ)^8343 ≤ (13749942201491/100000000000000 : ℝ)^6295 := by
    have hnat : (55945697 : ℕ)^8343*100000000000000^6295 ≤ 13749942201491^6295*250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55945697 250000000 13749942201491 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216645629/10000000000 : ℝ)^8343 ≤ (42213184876717/100000000000000 : ℝ)^6295 := by
    have hnat : (5216645629 : ℕ)^8343*100000000000000^6295 ≤ 42213184876717^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216645629 10000000000 42213184876717 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346451519/2500000000 : ℝ)^8343 ≤ (22018436450931/50000000000000 : ℝ)^6295 := by
    have hnat : (1346451519 : ℕ)^8343*50000000000000^6295 ≤ 22018436450931^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346451519 2500000000 22018436450931 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55945697/250000000 : ℝ), (5216645629/10000000000 : ℝ), (1346451519/2500000000 : ℝ)] ![(13749942201491/100000000000000 : ℝ), (42213184876717/100000000000000 : ℝ), (22018436450931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55945697/250000000 : ℝ)|^8343 ≤ (13749942201491/100000000000000 : ℝ)^6295
        have hw : |(-55945697/250000000 : ℝ)|=(55945697/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216645629/10000000000 : ℝ)|^8343 ≤ (42213184876717/100000000000000 : ℝ)^6295
        have hw : |(5216645629/10000000000 : ℝ)|=(5216645629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346451519/2500000000 : ℝ)|^8343 ≤ (22018436450931/50000000000000 : ℝ)^6295
        have hw : |(1346451519/2500000000 : ℝ)|=(1346451519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_9 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322316489/2500000000 : ℝ)*x 0 + (-1070643973/5000000000 : ℝ)*x 1 + (1346451443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322316489/2500000000 : ℝ)^8343 ≤ (8598754184903/20000000000000 : ℝ)^6295 := by
    have hnat : (1322316489 : ℕ)^8343*20000000000000^6295 ≤ 8598754184903^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322316489 2500000000 8598754184903 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070643973/5000000000 : ℝ)^8343 ≤ (2593871889887/20000000000000 : ℝ)^6295 := by
    have hnat : (1070643973 : ℕ)^8343*20000000000000^6295 ≤ 2593871889887^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070643973 5000000000 2593871889887 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346451443/2500000000 : ℝ)^8343 ≤ (44036869607541/100000000000000 : ℝ)^6295 := by
    have hnat : (1346451443 : ℕ)^8343*100000000000000^6295 ≤ 44036869607541^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346451443 2500000000 44036869607541 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322316489/2500000000 : ℝ), (-1070643973/5000000000 : ℝ), (1346451443/2500000000 : ℝ)] ![(8598754184903/20000000000000 : ℝ), (2593871889887/20000000000000 : ℝ), (44036869607541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322316489/2500000000 : ℝ)|^8343 ≤ (8598754184903/20000000000000 : ℝ)^6295
        have hw : |(1322316489/2500000000 : ℝ)|=(1322316489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070643973/5000000000 : ℝ)|^8343 ≤ (2593871889887/20000000000000 : ℝ)^6295
        have hw : |(-1070643973/5000000000 : ℝ)|=(1070643973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346451443/2500000000 : ℝ)|^8343 ≤ (44036869607541/100000000000000 : ℝ)^6295
        have hw : |(1346451443/2500000000 : ℝ)|=(1346451443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_10 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644633093/5000000000 : ℝ)*x 0 + (5385805503/10000000000 : ℝ)*x 1 + (-267661/1250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644633093/5000000000 : ℝ)^8343 ≤ (8598754680461/20000000000000 : ℝ)^6295 := by
    have hnat : (2644633093 : ℕ)^8343*20000000000000^6295 ≤ 8598754680461^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644633093 5000000000 8598754680461 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385805503/10000000000 : ℝ)^8343 ≤ (44036866692501/100000000000000 : ℝ)^6295 := by
    have hnat : (5385805503 : ℕ)^8343*100000000000000^6295 ≤ 44036866692501^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385805503 10000000000 44036866692501 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267661/1250000 : ℝ)^8343 ≤ (12969359882909/100000000000000 : ℝ)^6295 := by
    have hnat : (267661 : ℕ)^8343*100000000000000^6295 ≤ 12969359882909^6295*1250000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267661 1250000 12969359882909 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644633093/5000000000 : ℝ), (5385805503/10000000000 : ℝ), (-267661/1250000 : ℝ)] ![(8598754680461/20000000000000 : ℝ), (44036866692501/100000000000000 : ℝ), (12969359882909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644633093/5000000000 : ℝ)|^8343 ≤ (8598754680461/20000000000000 : ℝ)^6295
        have hw : |(2644633093/5000000000 : ℝ)|=(2644633093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385805503/10000000000 : ℝ)|^8343 ≤ (44036866692501/100000000000000 : ℝ)^6295
        have hw : |(5385805503/10000000000 : ℝ)|=(5385805503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267661/1250000 : ℝ)|^8343 ≤ (12969359882909/100000000000000 : ℝ)^6295
        have hw : |(-267661/1250000 : ℝ)|=(267661/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_11 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (898505291/2000000000 : ℝ)*x 0 + (1075255839/2500000000 : ℝ)*x 1 + (4301023097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898505291/2000000000 : ℝ)^8343 ≤ (34628429357167/100000000000000 : ℝ)^6295 := by
    have hnat : (898505291 : ℕ)^8343*100000000000000^6295 ≤ 34628429357167^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898505291 2000000000 34628429357167 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075255839/2500000000 : ℝ)^8343 ≤ (16342893311211/50000000000000 : ℝ)^6295 := by
    have hnat : (1075255839 : ℕ)^8343*50000000000000^6295 ≤ 16342893311211^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075255839 2500000000 16342893311211 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4301023097/10000000000 : ℝ)^8343 ≤ (32685784013787/100000000000000 : ℝ)^6295 := by
    have hnat : (4301023097 : ℕ)^8343*100000000000000^6295 ≤ 32685784013787^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301023097 10000000000 32685784013787 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898505291/2000000000 : ℝ), (1075255839/2500000000 : ℝ), (4301023097/10000000000 : ℝ)] ![(34628429357167/100000000000000 : ℝ), (16342893311211/50000000000000 : ℝ), (32685784013787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898505291/2000000000 : ℝ)|^8343 ≤ (34628429357167/100000000000000 : ℝ)^6295
        have hw : |(898505291/2000000000 : ℝ)|=(898505291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075255839/2500000000 : ℝ)|^8343 ≤ (16342893311211/50000000000000 : ℝ)^6295
        have hw : |(1075255839/2500000000 : ℝ)|=(1075255839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4301023097/10000000000 : ℝ)|^8343 ≤ (32685784013787/100000000000000 : ℝ)^6295
        have hw : |(4301023097/10000000000 : ℝ)|=(4301023097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_12 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1045006173/5000000000 : ℝ)*x 0 + (2719759431/5000000000 : ℝ)*x 1 + (2636598959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045006173/5000000000 : ℝ)^8343 ≤ (12559366423489/100000000000000 : ℝ)^6295 := by
    have hnat : (1045006173 : ℕ)^8343*100000000000000^6295 ≤ 12559366423489^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045006173 5000000000 12559366423489 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719759431/5000000000 : ℝ)^8343 ≤ (2788742375807/6250000000000 : ℝ)^6295 := by
    have hnat : (2719759431 : ℕ)^8343*6250000000000^6295 ≤ 2788742375807^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719759431 5000000000 2788742375807 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636598959/5000000000 : ℝ)^8343 ≤ (5352594444621/12500000000000 : ℝ)^6295 := by
    have hnat : (2636598959 : ℕ)^8343*12500000000000^6295 ≤ 5352594444621^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636598959 5000000000 5352594444621 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1045006173/5000000000 : ℝ), (2719759431/5000000000 : ℝ), (2636598959/5000000000 : ℝ)] ![(12559366423489/100000000000000 : ℝ), (2788742375807/6250000000000 : ℝ), (5352594444621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1045006173/5000000000 : ℝ)|^8343 ≤ (12559366423489/100000000000000 : ℝ)^6295
        have hw : |(-1045006173/5000000000 : ℝ)|=(1045006173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719759431/5000000000 : ℝ)|^8343 ≤ (2788742375807/6250000000000 : ℝ)^6295
        have hw : |(2719759431/5000000000 : ℝ)|=(2719759431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636598959/5000000000 : ℝ)|^8343 ≤ (5352594444621/12500000000000 : ℝ)^6295
        have hw : |(2636598959/5000000000 : ℝ)|=(2636598959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_13 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536881061/1000000000 : ℝ)*x 0 + (-27320303/125000000 : ℝ)*x 1 + (5273197537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536881061/1000000000 : ℝ)^8343 ≤ (43852794769643/100000000000000 : ℝ)^6295 := by
    have hnat : (536881061 : ℕ)^8343*100000000000000^6295 ≤ 43852794769643^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536881061 1000000000 43852794769643 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27320303/125000000 : ℝ)^8343 ≤ (13326453753947/100000000000000 : ℝ)^6295 := by
    have hnat : (27320303 : ℕ)^8343*100000000000000^6295 ≤ 13326453753947^6295*125000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27320303 125000000 13326453753947 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273197537/10000000000 : ℝ)^8343 ≤ (10705187864129/25000000000000 : ℝ)^6295 := by
    have hnat : (5273197537 : ℕ)^8343*25000000000000^6295 ≤ 10705187864129^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273197537 10000000000 10705187864129 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536881061/1000000000 : ℝ), (-27320303/125000000 : ℝ), (5273197537/10000000000 : ℝ)] ![(43852794769643/100000000000000 : ℝ), (13326453753947/100000000000000 : ℝ), (10705187864129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536881061/1000000000 : ℝ)|^8343 ≤ (43852794769643/100000000000000 : ℝ)^6295
        have hw : |(536881061/1000000000 : ℝ)|=(536881061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27320303/125000000 : ℝ)|^8343 ≤ (13326453753947/100000000000000 : ℝ)^6295
        have hw : |(-27320303/125000000 : ℝ)|=(27320303/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273197537/10000000000 : ℝ)|^8343 ≤ (10705187864129/25000000000000 : ℝ)^6295
        have hw : |(5273197537/10000000000 : ℝ)|=(5273197537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_14 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684405221/5000000000 : ℝ)*x 0 + (1318299469/2500000000 : ℝ)*x 1 + (-437124803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684405221/5000000000 : ℝ)^8343 ≤ (5481599118871/12500000000000 : ℝ)^6295 := by
    have hnat : (2684405221 : ℕ)^8343*12500000000000^6295 ≤ 5481599118871^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684405221 5000000000 5481599118871 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318299469/2500000000 : ℝ)^8343 ≤ (856415102099/2000000000000 : ℝ)^6295 := by
    have hnat : (1318299469 : ℕ)^8343*2000000000000^6295 ≤ 856415102099^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318299469 2500000000 856415102099 2000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437124803/2000000000 : ℝ)^8343 ≤ (13326451935719/100000000000000 : ℝ)^6295 := by
    have hnat : (437124803 : ℕ)^8343*100000000000000^6295 ≤ 13326451935719^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437124803 2000000000 13326451935719 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684405221/5000000000 : ℝ), (1318299469/2500000000 : ℝ), (-437124803/2000000000 : ℝ)] ![(5481599118871/12500000000000 : ℝ), (856415102099/2000000000000 : ℝ), (13326451935719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684405221/5000000000 : ℝ)|^8343 ≤ (5481599118871/12500000000000 : ℝ)^6295
        have hw : |(2684405221/5000000000 : ℝ)|=(2684405221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318299469/2500000000 : ℝ)|^8343 ≤ (856415102099/2000000000000 : ℝ)^6295
        have hw : |(1318299469/2500000000 : ℝ)|=(1318299469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437124803/2000000000 : ℝ)|^8343 ≤ (13326451935719/100000000000000 : ℝ)^6295
        have hw : |(-437124803/2000000000 : ℝ)|=(437124803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_box_15 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (529657173/1250000000 : ℝ)*x 0 + (177146203/400000000 : ℝ)*x 1 + (4428655461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529657173/1250000000 : ℝ)^8343 ≤ (16022546454521/50000000000000 : ℝ)^6295 := by
    have hnat : (529657173 : ℕ)^8343*50000000000000^6295 ≤ 16022546454521^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529657173 1250000000 16022546454521 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177146203/400000000 : ℝ)^8343 ≤ (33977451579/100000000000 : ℝ)^6295 := by
    have hnat : (177146203 : ℕ)^8343*100000000000^6295 ≤ 33977451579^6295*400000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177146203 400000000 33977451579 100000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4428655461/10000000000 : ℝ)^8343 ≤ (33977455503937/100000000000000 : ℝ)^6295 := by
    have hnat : (4428655461 : ℕ)^8343*100000000000000^6295 ≤ 33977455503937^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4428655461 10000000000 33977455503937 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529657173/1250000000 : ℝ), (177146203/400000000 : ℝ), (4428655461/10000000000 : ℝ)] ![(16022546454521/50000000000000 : ℝ), (33977451579/100000000000 : ℝ), (33977455503937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529657173/1250000000 : ℝ)|^8343 ≤ (16022546454521/50000000000000 : ℝ)^6295
        have hw : |(529657173/1250000000 : ℝ)|=(529657173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177146203/400000000 : ℝ)|^8343 ≤ (33977451579/100000000000 : ℝ)^6295
        have hw : |(177146203/400000000 : ℝ)|=(177146203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4428655461/10000000000 : ℝ)|^8343 ≤ (33977455503937/100000000000000 : ℝ)^6295
        have hw : |(4428655461/10000000000 : ℝ)|=(4428655461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7779/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11861/20000 : ℝ) ∧ (79833/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41571/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2841/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2841/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2841/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2841/25000 : ℝ) ^ (4171/1024 : ℝ) ≤ (14221648520212727/100000000000000000000 : ℝ) := by
    have hpowers : (2841/25000 : ℝ)^4171 ≤ (14221648520212727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2841 : ℕ)^4171*100000000000000000000^1024 ≤ 14221648520212727^1024*25000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2841 25000 14221648520212727 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2841/25000 : ℝ)) (X := (14221648520212727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (16889894237116133/50000000000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^4171 ≤ (16889894237116133/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14053 : ℕ)^4171*50000000000000000000^1024 ≤ 16889894237116133^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 16889894237116133 50000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (16889894237116133/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014221648520212727/50000000000000000000 : ℝ) ≤ (10000698221324083/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50014221648520212727/50000000000000000000 : ℝ)^1024 ≤ (10000698221324083/10000000000000000 : ℝ)^4171 := by
      have hnat : (50014221648520212727 : ℕ)^1024*10000000000000000^4171 ≤ 10000698221324083^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014221648520212727 50000000000000000000 10000698221324083 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000698221324083/10000000000000000 : ℝ)) (X := (50014221648520212727/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048001436994444993/100000000000000000000 : ℝ) ≤ (2000235648875849/2000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (100048001436994444993/100000000000000000000 : ℝ)^1024 ≤ (2000235648875849/2000000000000000 : ℝ)^4171 := by
      have hnat : (100048001436994444993 : ℕ)^1024*2000000000000000^4171 ≤ 2000235648875849^4171*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048001436994444993 100000000000000000000 2000235648875849 2000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000235648875849/2000000000000000 : ℝ)) (X := (100048001436994444993/100000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016889894237116133/25000000000000000000 : ℝ) ≤ (10001658267434407/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (25016889894237116133/25000000000000000000 : ℝ)^1024 ≤ (10001658267434407/10000000000000000 : ℝ)^4171 := by
      have hnat : (25016889894237116133 : ℕ)^1024*10000000000000000^4171 ≤ 10001658267434407^4171*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016889894237116133 25000000000000000000 10001658267434407 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001658267434407/10000000000000000 : ℝ)) (X := (25016889894237116133/25000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14221648520212727/100000000000000000000 : ℝ) ≤ ((26880967553142737251/26890000000000000000 : ℝ)+2*(240011527581/134450000000000 : ℝ)*(2841/25000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (26880967553142737251/26890000000000000000 : ℝ)+2*(240011527581/134450000000000 : ℝ)*(2841/25000 : ℝ)=(10000698221324083/10000000000000000 : ℝ) by norm_num, show 1+2*(14221648520212727/100000000000000000000 : ℝ)=(50014221648520212727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16889894237116133/50000000000000000000 : ℝ)+(14221648520212727/100000000000000000000 : ℝ) ≤ ((26880967553142737251/26890000000000000000 : ℝ)+(240011527581/134450000000000 : ℝ)*((14053/100000 : ℝ)+(2841/25000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (26880967553142737251/26890000000000000000 : ℝ)+(240011527581/134450000000000 : ℝ)*((14053/100000 : ℝ)+(2841/25000 : ℝ))=(2000235648875849/2000000000000000 : ℝ) by norm_num, show 1+(16889894237116133/50000000000000000000 : ℝ)+(14221648520212727/100000000000000000000 : ℝ)=(100048001436994444993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16889894237116133/50000000000000000000 : ℝ) ≤ ((26880967553142737251/26890000000000000000 : ℝ)+2*(240011527581/134450000000000 : ℝ)*(14053/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (26880967553142737251/26890000000000000000 : ℝ)+2*(240011527581/134450000000000 : ℝ)*(14053/100000 : ℝ)=(10001658267434407/10000000000000000 : ℝ) by norm_num, show 1+2*(16889894237116133/50000000000000000000 : ℝ)=(25016889894237116133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26880967553142737251/26890000000000000000 : ℝ)*(X 1 0+X 2 0)+(240011527581/134450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (26880967553142737251/26890000000000000000 : ℝ)) (alpha := (240011527581/134450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26880967553142737251/26890000000000000000 : ℝ)*(X 0 1+X 2 1)+(240011527581/134450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (26880967553142737251/26890000000000000000 : ℝ)) (alpha := (240011527581/134450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26880967553142737251/26890000000000000000 : ℝ)*(X 0 2+X 1 2)+(240011527581/134450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (2841/25000 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (26880967553142737251/26890000000000000000 : ℝ)) (alpha := (240011527581/134450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1018218537/5000000000 : ℝ)*X 0 0+(1075239213/2000000000 : ℝ)*X 0 1+(1344049117/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296056753/10000000000 : ℝ)*X 1 0+(-536284833/2500000000 : ℝ)*X 1 1+(5376196831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((662007201/1250000000 : ℝ)*X 2 0+(5376196289/10000000000 : ℝ)*X 2 1+(-429027783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2235506027/5000000000 : ℝ)*X 0 0+(2155960509/5000000000 : ℝ)*X 0 1+(2155960461/5000000000 : ℝ)*X 0 2+(2235506027/5000000000 : ℝ)*X 1 0+(2155960509/5000000000 : ℝ)*X 1 1+(2155960461/5000000000 : ℝ)*X 1 2+(2235506027/5000000000 : ℝ)*X 2 0+(2155960509/5000000000 : ℝ)*X 2 1+(2155960461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2291088451/10000000000 : ℝ)*X 0 0+(330077513/625000000 : ℝ)*X 0 1+(5281241013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363131351/10000000000 : ℝ)*X 1 0+(-1091258249/5000000000 : ℝ)*X 1 1+(660155007/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363131349/10000000000 : ℝ)*X 2 0+(5281239917/10000000000 : ℝ)*X 2 1+(-2182516687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127861477/5000000000 : ℝ)*X 0 0+(2209772953/5000000000 : ℝ)*X 0 1+(4419543583/10000000000 : ℝ)*X 0 2+(2127861477/5000000000 : ℝ)*X 1 0+(2209772953/5000000000 : ℝ)*X 1 1+(4419543583/10000000000 : ℝ)*X 1 2+(2127861477/5000000000 : ℝ)*X 2 0+(2209772953/5000000000 : ℝ)*X 2 1+(4419543583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-55945697/250000000 : ℝ)*X 0 0+(5216645629/10000000000 : ℝ)*X 0 1+(1346451519/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322316489/2500000000 : ℝ)*X 1 0+(-1070643973/5000000000 : ℝ)*X 1 1+(1346451443/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644633093/5000000000 : ℝ)*X 2 0+(5385805503/10000000000 : ℝ)*X 2 1+(-267661/1250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((898505291/2000000000 : ℝ)*X 0 0+(1075255839/2500000000 : ℝ)*X 0 1+(4301023097/10000000000 : ℝ)*X 0 2+(898505291/2000000000 : ℝ)*X 1 0+(1075255839/2500000000 : ℝ)*X 1 1+(4301023097/10000000000 : ℝ)*X 1 2+(898505291/2000000000 : ℝ)*X 2 0+(1075255839/2500000000 : ℝ)*X 2 1+(4301023097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1045006173/5000000000 : ℝ)*X 0 0+(2719759431/5000000000 : ℝ)*X 0 1+(2636598959/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((536881061/1000000000 : ℝ)*X 1 0+(-27320303/125000000 : ℝ)*X 1 1+(5273197537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684405221/5000000000 : ℝ)*X 2 0+(1318299469/2500000000 : ℝ)*X 2 1+(-437124803/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((529657173/1250000000 : ℝ)*X 0 0+(177146203/400000000 : ℝ)*X 0 1+(4428655461/10000000000 : ℝ)*X 0 2+(529657173/1250000000 : ℝ)*X 1 0+(177146203/400000000 : ℝ)*X 1 1+(4428655461/10000000000 : ℝ)*X 1 2+(529657173/1250000000 : ℝ)*X 2 0+(177146203/400000000 : ℝ)*X 2 1+(4428655461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7779/12500 : ℝ) ≤ (-418338539362126166883333868499193/672250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10969933/12500000000000 : ℝ)*(upper0) + (312445231/50000000000000 : ℝ)*(upper1) + (3862991/20000000000000 : ℝ)*(upper2) + (80799473/50000000000000 : ℝ)*(upper3) + (1963535870160827/50000000000000 : ℝ)*(major0) + (1963535870160827/50000000000000 : ℝ)*(major1) + (1963535870160827/50000000000000 : ℝ)*(major2) + (2062418357/50000000000000 : ℝ)*(sp1) + (3423997071/50000000000000 : ℝ)*(sp2) + (434899347/50000000000000 : ℝ)*(sp3) + (5250361914208351/100000000000000 : ℝ)*(sp4) + (5250357789371637/100000000000000 : ℝ)*(sp5) + (5250355066214209/100000000000000 : ℝ)*(sp6) + (13122619496411/500000000000 : ℝ)*(sp7) + (524904953816179/20000000000000 : ℝ)*(f.failure) + (5250361914208351/100000000000000 : ℝ)*(f.sum) + (77287065624073/13445000000000000000000000000 : ℝ)*base65 + (16989183543121266577/1344500000000000000000000000000000 : ℝ)*base67 + (10966096031591766577/1344500000000000000000000000000000 : ℝ)*base69 + (11451595688798766577/1344500000000000000000000000000000 : ℝ)*base71 + (31623902056469/6722500000000000000000000000 : ℝ)*base73 + (11146735733478266577/1344500000000000000000000000000000 : ℝ)*base75 + (4555992593762766577/1344500000000000000000000000000000 : ℝ)*base77 + (14075729105827766577/1344500000000000000000000000000000 : ℝ)*base79 + (146656072817973/13445000000000000000000000000 : ℝ)*base81 + (2245069/1000000000000000000000 : ℝ)*base89 + (2245069/1000000000000000000000 : ℝ)*base91 + (2245069/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11861/20000 : ℝ) ≤ (19934597952369009513167392695003/33612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107270191/100000000000000 : ℝ)*(lower1) + (152987821/100000000000000 : ℝ)*(lower2) + (61586189/50000000000000 : ℝ)*(lower3) + (59136597/25000000000000 : ℝ)*(upper4) + (199567753027751/5000000000000 : ℝ)*(major0) + (199567753027751/5000000000000 : ℝ)*(major1) + (199567753027751/5000000000000 : ℝ)*(major2) + (1059090950009431/20000000000000 : ℝ)*(sp0) + (5295432831948381/100000000000000 : ℝ)*(sp1) + (5295442258185439/100000000000000 : ℝ)*(sp2) + (1333738975633433/50000000000000 : ℝ)*(sp3) + (10959049387/50000000000000 : ℝ)*(sp5) + (3122965429/25000000000000 : ℝ)*(sp6) + (4193744601/50000000000000 : ℝ)*(sp7) + (666871584689017/25000000000000 : ℝ)*(f.failure) + (1059090950009431/20000000000000 : ℝ)*(f.sum) + (514107117173/268900000000000000000000000 : ℝ)*base66 + (1850984057033097499/134450000000000000000000000000000 : ℝ)*base68 + (5563144265792447499/134450000000000000000000000000000 : ℝ)*base70 + (562218202272897499/134450000000000000000000000000000 : ℝ)*base72 + (83698077349/42015625000000000000000000 : ℝ)*base74 + (1604482283939197499/134450000000000000000000000000000 : ℝ)*base76 + (5562413002638052501/134450000000000000000000000000000 : ℝ)*base77 + (1304244257110697499/134450000000000000000000000000000 : ℝ)*base80 + (87410560004001/2689000000000000000000000000 : ℝ)*base82 + (19532487/1250000000000000000000 : ℝ)*base89 + (19532487/1250000000000000000000 : ℝ)*base91 + (19532487/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79833/100000 : ℝ) ≤ (134172855983088672006800636324979/168062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (649047/25000000000000 : ℝ)*(upper0) + (7347879/12500000000000 : ℝ)*(upper1) + (8531741/20000000000000 : ℝ)*(upper4) + (557396244198243/12500000000000 : ℝ)*(major0) + (557396244198243/12500000000000 : ℝ)*(major1) + (557396244198243/12500000000000 : ℝ)*(major2) + (137403533289/100000000000000 : ℝ)*(sp1) + (22596873459/20000000000000 : ℝ)*(sp3) + (938320277/25000000000000 : ℝ)*(sp4) + (1182314194646949/20000000000000 : ℝ)*(sp8) + (738932037686001/12500000000000 : ℝ)*(sp9) + (5911593705021297/100000000000000 : ℝ)*(sp10) + (1490010759779649/50000000000000 : ℝ)*(sp11) + (4744626361/25000000000000 : ℝ)*(sp12) + (2980134503926593/100000000000000 : ℝ)*(f.failure) + (5911593705021297/100000000000000 : ℝ)*(f.sum) + (7960748454317/3361250000000000000000000000 : ℝ)*base65 + (3505756572227925007/336125000000000000000000000000000 : ℝ)*base68 + (2340944061904550007/336125000000000000000000000000000 : ℝ)*base70 + (2373915506083324993/336125000000000000000000000000000 : ℝ)*base71 + (44272435354719/6722500000000000000000000000 : ℝ)*base73 + (3774359449828425007/336125000000000000000000000000000 : ℝ)*base76 + (2203649042189199993/336125000000000000000000000000000 : ℝ)*base77 + (2468993326636175007/336125000000000000000000000000000 : ℝ)*base80 + (3801893015151/1680625000000000000000000000 : ℝ)*base81 + (5828223/5000000000000000000000 : ℝ)*base89 + (5828223/5000000000000000000000 : ℝ)*base91 + (5828223/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41571/50000 : ℝ) ≤ (-27945405140480463109665267367323/33612500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14142057/100000000000000 : ℝ)*(lower0) + (21052773/12500000000000 : ℝ)*(lower1) + (38051331/50000000000000 : ℝ)*(lower2) + (224707279117309/5000000000000 : ℝ)*(major0) + (224707279117309/5000000000000 : ℝ)*(major1) + (224707279117309/5000000000000 : ℝ)*(major2) + (2107305639/12500000000000 : ℝ)*(sp0) + (355073946197/50000000000000 : ℝ)*(sp5) + (398300927187/100000000000000 : ℝ)*(sp6) + (22130115437/100000000000000 : ℝ)*(sp7) + (300623916858707/5000000000000 : ℝ)*(sp12) + (3005892523863429/50000000000000 : ℝ)*(sp13) + (187878027959127/3125000000000 : ℝ)*(sp14) + (30034871451587/1000000000000 : ℝ)*(sp15) + (375438659409267/12500000000000 : ℝ)*(f.failure) + (1503123798904813/25000000000000 : ℝ)*(f.sum) + (5753282256951/1344500000000000000000000000 : ℝ)*base65 + (754657633760922441/134450000000000000000000000000000 : ℝ)*base68 + (1476988917622172441/134450000000000000000000000000000 : ℝ)*base70 + (131296744766422441/134450000000000000000000000000000 : ℝ)*base72 + (45127884747289/1344500000000000000000000000 : ℝ)*base74 + (2292720982781472441/134450000000000000000000000000000 : ℝ)*base76 + (2087718507270927559/134450000000000000000000000000000 : ℝ)*base77 + (7771907875845272441/134450000000000000000000000000000 : ℝ)*base80 + (8884017750853/1344500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1819763/625000000000000000000 : ℝ)*base90 + (1819763/625000000000000000000 : ℝ)*base92 + (1819763/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1150_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11861/20000 : ℝ) else (79833/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41571/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1150_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1150_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11861/20000 : ℝ) else (79833/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41571/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1150_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2841/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(11861/20000 : ℝ) else (79833/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41571/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
