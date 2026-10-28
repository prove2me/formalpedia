-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:53:35.049732+00:00
-- url     : https://prove2.me/submissions/e0ca131c-a813-4cd1-889d-bdbee1cf1465

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
theorem support_rectangle_w1259_s0_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-231915741/1250000000 : ℝ)*x 0 + (1205536391/2000000000 : ℝ)*x 1 + (4795088919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231915741/1250000000 : ℝ)^2113 ≤ (10825822617411/100000000000000 : ℝ)^1601 := by
    have hnat : (231915741 : ℕ)^2113*100000000000000^1601 ≤ 10825822617411^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231915741 1250000000 10825822617411 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205536391/2000000000 : ℝ)^2113 ≤ (51267527953397/100000000000000 : ℝ)^1601 := by
    have hnat : (1205536391 : ℕ)^2113*100000000000000^1601 ≤ 51267527953397^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205536391 2000000000 51267527953397 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795088919/10000000000 : ℝ)^2113 ≤ (37906649414271/100000000000000 : ℝ)^1601 := by
    have hnat : (4795088919 : ℕ)^2113*100000000000000^1601 ≤ 37906649414271^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795088919 10000000000 37906649414271 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231915741/1250000000 : ℝ), (1205536391/2000000000 : ℝ), (4795088919/10000000000 : ℝ)] ![(10825822617411/100000000000000 : ℝ), (51267527953397/100000000000000 : ℝ), (37906649414271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231915741/1250000000 : ℝ)|^2113 ≤ (10825822617411/100000000000000 : ℝ)^1601
        have hw : |(-231915741/1250000000 : ℝ)|=(231915741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1205536391/2000000000 : ℝ)|^2113 ≤ (51267527953397/100000000000000 : ℝ)^1601
        have hw : |(1205536391/2000000000 : ℝ)|=(1205536391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795088919/10000000000 : ℝ)|^2113 ≤ (37906649414271/100000000000000 : ℝ)^1601
        have hw : |(4795088919/10000000000 : ℝ)|=(4795088919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5510201707/10000000000 : ℝ)*x 0 + (-2559515133/10000000000 : ℝ)*x 1 + (599386111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510201707/10000000000 : ℝ)^2113 ≤ (5692497429477/12500000000000 : ℝ)^1601 := by
    have hnat : (5510201707 : ℕ)^2113*12500000000000^1601 ≤ 5692497429477^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510201707 10000000000 5692497429477 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2559515133/10000000000 : ℝ)^2113 ≤ (4138342864001/25000000000000 : ℝ)^1601 := by
    have hnat : (2559515133 : ℕ)^2113*25000000000000^1601 ≤ 4138342864001^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559515133 10000000000 4138342864001 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599386111/1250000000 : ℝ)^2113 ≤ (7581329818167/20000000000000 : ℝ)^1601 := by
    have hnat : (599386111 : ℕ)^2113*20000000000000^1601 ≤ 7581329818167^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599386111 1250000000 7581329818167 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510201707/10000000000 : ℝ), (-2559515133/10000000000 : ℝ), (599386111/1250000000 : ℝ)] ![(5692497429477/12500000000000 : ℝ), (4138342864001/25000000000000 : ℝ), (7581329818167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510201707/10000000000 : ℝ)|^2113 ≤ (5692497429477/12500000000000 : ℝ)^1601
        have hw : |(5510201707/10000000000 : ℝ)|=(5510201707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2559515133/10000000000 : ℝ)|^2113 ≤ (4138342864001/25000000000000 : ℝ)^1601
        have hw : |(-2559515133/10000000000 : ℝ)|=(2559515133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(599386111/1250000000 : ℝ)|^2113 ≤ (7581329818167/20000000000000 : ℝ)^1601
        have hw : |(599386111/1250000000 : ℝ)|=(599386111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (344387609/625000000 : ℝ)*x 0 + (479508889/1000000000 : ℝ)*x 1 + (-2559515083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344387609/625000000 : ℝ)^2113 ≤ (45539979839401/100000000000000 : ℝ)^1601 := by
    have hnat : (344387609 : ℕ)^2113*100000000000000^1601 ≤ 45539979839401^1601*625000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344387609 625000000 45539979839401 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479508889/1000000000 : ℝ)^2113 ≤ (37906649111701/100000000000000 : ℝ)^1601 := by
    have hnat : (479508889 : ℕ)^2113*100000000000000^1601 ≤ 37906649111701^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479508889 1000000000 37906649111701 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559515083/10000000000 : ℝ)^2113 ≤ (16553371029221/100000000000000 : ℝ)^1601 := by
    have hnat : (2559515083 : ℕ)^2113*100000000000000^1601 ≤ 16553371029221^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559515083 10000000000 16553371029221 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344387609/625000000 : ℝ), (479508889/1000000000 : ℝ), (-2559515083/10000000000 : ℝ)] ![(45539979839401/100000000000000 : ℝ), (37906649111701/100000000000000 : ℝ), (16553371029221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344387609/625000000 : ℝ)|^2113 ≤ (45539979839401/100000000000000 : ℝ)^1601
        have hw : |(344387609/625000000 : ℝ)|=(344387609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(479508889/1000000000 : ℝ)|^2113 ≤ (37906649111701/100000000000000 : ℝ)^1601
        have hw : |(479508889/1000000000 : ℝ)|=(479508889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2559515083/10000000000 : ℝ)|^2113 ≤ (16553371029221/100000000000000 : ℝ)^1601
        have hw : |(-2559515083/10000000000 : ℝ)|=(2559515083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4191689639/10000000000 : ℝ)*x 0 + (3116265427/10000000000 : ℝ)*x 1 + (2812438663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191689639/10000000000 : ℝ)^2113 ≤ (31741621765843/100000000000000 : ℝ)^1601 := by
    have hnat : (4191689639 : ℕ)^2113*100000000000000^1601 ≤ 31741621765843^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191689639 10000000000 31741621765843 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116265427/10000000000 : ℝ)^2113 ≤ (1341462973491/6250000000000 : ℝ)^1601 := by
    have hnat : (3116265427 : ℕ)^2113*6250000000000^1601 ≤ 1341462973491^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116265427 10000000000 1341462973491 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812438663/5000000000 : ℝ)^2113 ≤ (46794970641109/100000000000000 : ℝ)^1601 := by
    have hnat : (2812438663 : ℕ)^2113*100000000000000^1601 ≤ 46794970641109^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812438663 5000000000 46794970641109 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191689639/10000000000 : ℝ), (3116265427/10000000000 : ℝ), (2812438663/5000000000 : ℝ)] ![(31741621765843/100000000000000 : ℝ), (1341462973491/6250000000000 : ℝ), (46794970641109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191689639/10000000000 : ℝ)|^2113 ≤ (31741621765843/100000000000000 : ℝ)^1601
        have hw : |(4191689639/10000000000 : ℝ)|=(4191689639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116265427/10000000000 : ℝ)|^2113 ≤ (1341462973491/6250000000000 : ℝ)^1601
        have hw : |(3116265427/10000000000 : ℝ)|=(3116265427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812438663/5000000000 : ℝ)|^2113 ≤ (46794970641109/100000000000000 : ℝ)^1601
        have hw : |(2812438663/5000000000 : ℝ)|=(2812438663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-372027049/2000000000 : ℝ)*x 0 + (4826819559/10000000000 : ℝ)*x 1 + (5994829297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372027049/2000000000 : ℝ)^2113 ≤ (1357859332227/12500000000000 : ℝ)^1601 := by
    have hnat : (372027049 : ℕ)^2113*12500000000000^1601 ≤ 1357859332227^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372027049 2000000000 1357859332227 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4826819559/10000000000 : ℝ)^2113 ≤ (9559514610017/25000000000000 : ℝ)^1601 := by
    have hnat : (4826819559 : ℕ)^2113*25000000000000^1601 ≤ 9559514610017^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4826819559 10000000000 9559514610017 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5994829297/10000000000 : ℝ)^2113 ≤ (25449533444453/50000000000000 : ℝ)^1601 := by
    have hnat : (5994829297 : ℕ)^2113*50000000000000^1601 ≤ 25449533444453^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994829297 10000000000 25449533444453 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372027049/2000000000 : ℝ), (4826819559/10000000000 : ℝ), (5994829297/10000000000 : ℝ)] ![(1357859332227/12500000000000 : ℝ), (9559514610017/25000000000000 : ℝ), (25449533444453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372027049/2000000000 : ℝ)|^2113 ≤ (1357859332227/12500000000000 : ℝ)^1601
        have hw : |(-372027049/2000000000 : ℝ)|=(372027049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4826819559/10000000000 : ℝ)|^2113 ≤ (9559514610017/25000000000000 : ℝ)^1601
        have hw : |(4826819559/10000000000 : ℝ)|=(4826819559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5994829297/10000000000 : ℝ)|^2113 ≤ (25449533444453/50000000000000 : ℝ)^1601
        have hw : |(5994829297/10000000000 : ℝ)|=(5994829297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587379977/5000000000 : ℝ)*x 0 + (-54390893/400000000 : ℝ)*x 1 + (5994831699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587379977/5000000000 : ℝ)^2113 ≤ (41917199690349/100000000000000 : ℝ)^1601 := by
    have hnat : (2587379977 : ℕ)^2113*100000000000000^1601 ≤ 41917199690349^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587379977 5000000000 41917199690349 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54390893/400000000 : ℝ)^2113 ≤ (448981655599/6250000000000 : ℝ)^1601 := by
    have hnat : (54390893 : ℕ)^2113*6250000000000^1601 ≤ 448981655599^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54390893 400000000 448981655599 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5994831699/10000000000 : ℝ)^2113 ≤ (25449546902567/50000000000000 : ℝ)^1601 := by
    have hnat : (5994831699 : ℕ)^2113*50000000000000^1601 ≤ 25449546902567^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994831699 10000000000 25449546902567 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587379977/5000000000 : ℝ), (-54390893/400000000 : ℝ), (5994831699/10000000000 : ℝ)] ![(41917199690349/100000000000000 : ℝ), (448981655599/6250000000000 : ℝ), (25449546902567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587379977/5000000000 : ℝ)|^2113 ≤ (41917199690349/100000000000000 : ℝ)^1601
        have hw : |(2587379977/5000000000 : ℝ)|=(2587379977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54390893/400000000 : ℝ)|^2113 ≤ (448981655599/6250000000000 : ℝ)^1601
        have hw : |(-54390893/400000000 : ℝ)|=(54390893/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5994831699/10000000000 : ℝ)|^2113 ≤ (25449546902567/50000000000000 : ℝ)^1601
        have hw : |(5994831699/10000000000 : ℝ)|=(5994831699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587380497/5000000000 : ℝ)*x 0 + (5994829717/10000000000 : ℝ)*x 1 + (-339943479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587380497/5000000000 : ℝ)^2113 ≤ (20958605404391/50000000000000 : ℝ)^1601 := by
    have hnat : (2587380497 : ℕ)^2113*50000000000000^1601 ≤ 20958605404391^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587380497 5000000000 20958605404391 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5994829717/10000000000 : ℝ)^2113 ≤ (50899071595323/100000000000000 : ℝ)^1601 := by
    have hnat : (5994829717 : ℕ)^2113*100000000000000^1601 ≤ 50899071595323^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5994829717 10000000000 50899071595323 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339943479/2500000000 : ℝ)^2113 ≤ (3591858791443/50000000000000 : ℝ)^1601 := by
    have hnat : (339943479 : ℕ)^2113*50000000000000^1601 ≤ 3591858791443^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339943479 2500000000 3591858791443 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587380497/5000000000 : ℝ), (5994829717/10000000000 : ℝ), (-339943479/2500000000 : ℝ)] ![(20958605404391/50000000000000 : ℝ), (50899071595323/100000000000000 : ℝ), (3591858791443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587380497/5000000000 : ℝ)|^2113 ≤ (20958605404391/50000000000000 : ℝ)^1601
        have hw : |(2587380497/5000000000 : ℝ)|=(2587380497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5994829717/10000000000 : ℝ)|^2113 ≤ (50899071595323/100000000000000 : ℝ)^1601
        have hw : |(5994829717/10000000000 : ℝ)|=(5994829717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339943479/2500000000 : ℝ)|^2113 ≤ (3591858791443/50000000000000 : ℝ)^1601
        have hw : |(-339943479/2500000000 : ℝ)|=(339943479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s0_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (420147999/1000000000 : ℝ)*x 0 + (5560303947/10000000000 : ℝ)*x 1 + (3183122157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420147999/1000000000 : ℝ)^2113 ≤ (1989969065187/6250000000000 : ℝ)^1601 := by
    have hnat : (420147999 : ℕ)^2113*6250000000000^1601 ≤ 1989969065187^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420147999 1000000000 1989969065187 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5560303947/10000000000 : ℝ)^2113 ≤ (46087272965801/100000000000000 : ℝ)^1601 := by
    have hnat : (5560303947 : ℕ)^2113*100000000000000^1601 ≤ 46087272965801^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560303947 10000000000 46087272965801 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183122157/10000000000 : ℝ)^2113 ≤ (22073221972969/100000000000000 : ℝ)^1601 := by
    have hnat : (3183122157 : ℕ)^2113*100000000000000^1601 ≤ 22073221972969^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183122157 10000000000 22073221972969 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420147999/1000000000 : ℝ), (5560303947/10000000000 : ℝ), (3183122157/10000000000 : ℝ)] ![(1989969065187/6250000000000 : ℝ), (46087272965801/100000000000000 : ℝ), (22073221972969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420147999/1000000000 : ℝ)|^2113 ≤ (1989969065187/6250000000000 : ℝ)^1601
        have hw : |(420147999/1000000000 : ℝ)|=(420147999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5560303947/10000000000 : ℝ)|^2113 ≤ (46087272965801/100000000000000 : ℝ)^1601
        have hw : |(5560303947/10000000000 : ℝ)|=(5560303947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183122157/10000000000 : ℝ)|^2113 ≤ (22073221972969/100000000000000 : ℝ)^1601
        have hw : |(3183122157/10000000000 : ℝ)|=(3183122157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (443/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27373/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8451/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8451 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8451*1^2048 ≤ 0^2048*1^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8451/2048 : ℝ) ≤ (1139946707715237749/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8451 ≤ (1139946707715237749/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8451*50000000000000000000^2048 ≤ 1139946707715237749^2048*5^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1139946707715237749 50000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1139946707715237749/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8451 := by
      have hnat : (1 : ℕ)^2048*1^8451 ≤ 1^8451*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51139946707715237749/50000000000000000000 : ℝ) ≤ (10054779603372009/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (51139946707715237749/50000000000000000000 : ℝ)^2048 ≤ (10054779603372009/10000000000000000 : ℝ)^8451 := by
      have hnat : (51139946707715237749 : ℕ)^2048*10000000000000000^8451 ≤ 10054779603372009^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51139946707715237749 50000000000000000000 10054779603372009 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054779603372009/10000000000000000 : ℝ)) (X := (51139946707715237749/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26139946707715237749/25000000000000000000 : ℝ) ≤ (5054779603372009/5000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (26139946707715237749/25000000000000000000 : ℝ)^2048 ≤ (5054779603372009/5000000000000000 : ℝ)^8451 := by
      have hnat : (26139946707715237749 : ℕ)^2048*5000000000000000^8451 ≤ 5054779603372009^8451*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26139946707715237749 25000000000000000000 5054779603372009 5000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054779603372009/5000000000000000 : ℝ)) (X := (26139946707715237749/25000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54779603372009/4000000000000000 : ℝ)*(0 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54779603372009/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1139946707715237749/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54779603372009/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (1 : ℝ)+(54779603372009/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054779603372009/10000000000000000 : ℝ) by norm_num, show 1+(1139946707715237749/50000000000000000000 : ℝ)+(0 : ℝ)=(51139946707715237749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1139946707715237749/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54779603372009/4000000000000000 : ℝ)*(2/5 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54779603372009/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054779603372009/5000000000000000 : ℝ) by norm_num, show 1+2*(1139946707715237749/50000000000000000000 : ℝ)=(26139946707715237749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54779603372009/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54779603372009/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54779603372009/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54779603372009/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54779603372009/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54779603372009/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-231915741/1250000000 : ℝ)*X 0 0+(1205536391/2000000000 : ℝ)*X 0 1+(4795088919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5510201707/10000000000 : ℝ)*X 1 0+(-2559515133/10000000000 : ℝ)*X 1 1+(599386111/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344387609/625000000 : ℝ)*X 2 0+(479508889/1000000000 : ℝ)*X 2 1+(-2559515083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4191689639/10000000000 : ℝ)*X 0 0+(3116265427/10000000000 : ℝ)*X 0 1+(2812438663/5000000000 : ℝ)*X 0 2+(4191689639/10000000000 : ℝ)*X 1 0+(3116265427/10000000000 : ℝ)*X 1 1+(2812438663/5000000000 : ℝ)*X 1 2+(4191689639/10000000000 : ℝ)*X 2 0+(3116265427/10000000000 : ℝ)*X 2 1+(2812438663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372027049/2000000000 : ℝ)*X 0 0+(4826819559/10000000000 : ℝ)*X 0 1+(5994829297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587379977/5000000000 : ℝ)*X 1 0+(-54390893/400000000 : ℝ)*X 1 1+(5994831699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587380497/5000000000 : ℝ)*X 2 0+(5994829717/10000000000 : ℝ)*X 2 1+(-339943479/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420147999/1000000000 : ℝ)*X 0 0+(5560303947/10000000000 : ℝ)*X 0 1+(3183122157/10000000000 : ℝ)*X 0 2+(420147999/1000000000 : ℝ)*X 1 0+(5560303947/10000000000 : ℝ)*X 1 1+(3183122157/10000000000 : ℝ)*X 1 2+(420147999/1000000000 : ℝ)*X 2 0+(5560303947/10000000000 : ℝ)*X 2 1+(3183122157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73920166669447781108979/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1472493/6250000000000 : ℝ)*(base1) + (365007237/100000000000000 : ℝ)*(base19) + (170424429/50000000000000 : ℝ)*(base23) + (14803053/50000000000000 : ℝ)*(base24) + (42303007/50000000000000 : ℝ)*(upper3) + (302481886073741/50000000000000 : ℝ)*(major0) + (302481886073741/50000000000000 : ℝ)*(major1) + (302481886073741/50000000000000 : ℝ)*(major2) + (811298978820173/100000000000000 : ℝ)*(sp0) + (202824838364549/25000000000000 : ℝ)*(sp1) + (811299348010469/100000000000000 : ℝ)*(sp2) + (398627153510929/100000000000000 : ℝ)*(sp3) + (190801287/25000000000000 : ℝ)*(sp4) + (149869649/25000000000000 : ℝ)*(sp7) + (199313888274707/50000000000000 : ℝ)*(f.failure) + (811299718465433/100000000000000 : ℝ)*(f.sum) + (313334042615669/100000000000000000000000000000 : ℝ)*base65 + (1331033620915669/200000000000000000000000000000 : ℝ)*base67 + (1645114955515669/200000000000000000000000000000 : ℝ)*base69 + (1336221380715669/200000000000000000000000000000 : ℝ)*base71 + (280132226615669/100000000000000000000000000000 : ℝ)*base73 + (1262206534515669/200000000000000000000000000000 : ℝ)*base75 + (1083877907915669/200000000000000000000000000000 : ℝ)*base77 + (605509328315669/200000000000000000000000000000 : ℝ)*base79 + (149386879415669/100000000000000000000000000000 : ℝ)*base81 + (2560999/500000000000000000000 : ℝ)*base89 + (2560999/500000000000000000000 : ℝ)*base91 + (2560999/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (397764068608561611702801/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123984577/50000000000000 : ℝ)*(base1) + (180656829/10000000000000 : ℝ)*(base19) + (98503023/5000000000000 : ℝ)*(base23) + (72243043/20000000000000 : ℝ)*(upper3) + (3153469/6250000000000 : ℝ)*(upper5) + (638411344094637/100000000000000 : ℝ)*(major0) + (638411344094637/100000000000000 : ℝ)*(major1) + (638411344094637/100000000000000 : ℝ)*(major2) + (349525719/10000000000000 : ℝ)*(sp1) + (1681502157/50000000000000 : ℝ)*(sp2) + (17123106824793/2000000000000 : ℝ)*(sp4) + (171229958289003/20000000000000 : ℝ)*(sp5) + (856149760205721/100000000000000 : ℝ)*(sp6) + (420667081773571/100000000000000 : ℝ)*(sp7) + (16826693189709/4000000000000 : ℝ)*(f.failure) + (171231018654099/20000000000000 : ℝ)*(f.sum) + (87181595184267/200000000000000000000000000000 : ℝ)*base66 + (3167834778015733/400000000000000000000000000000 : ℝ)*base67 + (1444938934015733/400000000000000000000000000000 : ℝ)*base69 + (2405275640815733/400000000000000000000000000000 : ℝ)*base71 + (594330694415733/200000000000000000000000000000 : ℝ)*base73 + (4928695272015733/400000000000000000000000000000 : ℝ)*base75 + (656548580815733/400000000000000000000000000000 : ℝ)*base77 + (2591287551215733/400000000000000000000000000000 : ℝ)*base79 + (450940183015733/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (231687/40000000000000000000 : ℝ)*base90 + (231687/40000000000000000000 : ℝ)*base92 + (231687/40000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1259_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27373/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1259_s1_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2051495321/10000000000 : ℝ)*x 0 + (1417841921/2500000000 : ℝ)*x 1 + (2512916077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051495321/10000000000 : ℝ)^2113 ≤ (12361483701429/100000000000000 : ℝ)^1601 := by
    have hnat : (2051495321 : ℕ)^2113*100000000000000^1601 ≤ 12361483701429^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051495321 10000000000 12361483701429 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417841921/2500000000 : ℝ)^2113 ≤ (47306098663473/100000000000000 : ℝ)^1601 := by
    have hnat : (1417841921 : ℕ)^2113*100000000000000^1601 ≤ 47306098663473^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417841921 2500000000 47306098663473 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512916077/5000000000 : ℝ)^2113 ≤ (40332417614073/100000000000000 : ℝ)^1601 := by
    have hnat : (2512916077 : ℕ)^2113*100000000000000^1601 ≤ 40332417614073^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512916077 5000000000 40332417614073 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2051495321/10000000000 : ℝ), (1417841921/2500000000 : ℝ), (2512916077/5000000000 : ℝ)] ![(12361483701429/100000000000000 : ℝ), (47306098663473/100000000000000 : ℝ), (40332417614073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2051495321/10000000000 : ℝ)|^2113 ≤ (12361483701429/100000000000000 : ℝ)^1601
        have hw : |(-2051495321/10000000000 : ℝ)|=(2051495321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417841921/2500000000 : ℝ)|^2113 ≤ (47306098663473/100000000000000 : ℝ)^1601
        have hw : |(1417841921/2500000000 : ℝ)|=(1417841921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512916077/5000000000 : ℝ)|^2113 ≤ (40332417614073/100000000000000 : ℝ)^1601
        have hw : |(2512916077/5000000000 : ℝ)|=(2512916077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2706369201/5000000000 : ℝ)*x 0 + (-2397860551/10000000000 : ℝ)*x 1 + (5025832331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706369201/5000000000 : ℝ)^2113 ≤ (22239948536137/50000000000000 : ℝ)^1601 := by
    have hnat : (2706369201 : ℕ)^2113*50000000000000^1601 ≤ 22239948536137^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706369201 5000000000 22239948536137 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397860551/10000000000 : ℝ)^2113 ≤ (3796920854959/25000000000000 : ℝ)^1601 := by
    have hnat : (2397860551 : ℕ)^2113*25000000000000^1601 ≤ 3796920854959^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397860551 10000000000 3796920854959 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025832331/10000000000 : ℝ)^2113 ≤ (10083104872189/25000000000000 : ℝ)^1601 := by
    have hnat : (5025832331 : ℕ)^2113*25000000000000^1601 ≤ 10083104872189^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025832331 10000000000 10083104872189 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706369201/5000000000 : ℝ), (-2397860551/10000000000 : ℝ), (5025832331/10000000000 : ℝ)] ![(22239948536137/50000000000000 : ℝ), (3796920854959/25000000000000 : ℝ), (10083104872189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706369201/5000000000 : ℝ)|^2113 ≤ (22239948536137/50000000000000 : ℝ)^1601
        have hw : |(2706369201/5000000000 : ℝ)|=(2706369201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2397860551/10000000000 : ℝ)|^2113 ≤ (3796920854959/25000000000000 : ℝ)^1601
        have hw : |(-2397860551/10000000000 : ℝ)|=(2397860551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025832331/10000000000 : ℝ)|^2113 ≤ (10083104872189/25000000000000 : ℝ)^1601
        have hw : |(5025832331/10000000000 : ℝ)|=(5025832331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5412738561/10000000000 : ℝ)*x 0 + (628229029/1250000000 : ℝ)*x 1 + (-239786047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412738561/10000000000 : ℝ)^2113 ≤ (4447989879673/10000000000000 : ℝ)^1601 := by
    have hnat : (5412738561 : ℕ)^2113*10000000000000^1601 ≤ 4447989879673^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412738561 10000000000 4447989879673 10000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628229029/1250000000 : ℝ)^2113 ≤ (10083104610051/25000000000000 : ℝ)^1601 := by
    have hnat : (628229029 : ℕ)^2113*25000000000000^1601 ≤ 10083104610051^1601*1250000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628229029 1250000000 10083104610051 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239786047/1000000000 : ℝ)^2113 ≤ (3796920685681/25000000000000 : ℝ)^1601 := by
    have hnat : (239786047 : ℕ)^2113*25000000000000^1601 ≤ 3796920685681^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239786047 1000000000 3796920685681 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412738561/10000000000 : ℝ), (628229029/1250000000 : ℝ), (-239786047/1000000000 : ℝ)] ![(4447989879673/10000000000000 : ℝ), (10083104610051/25000000000000 : ℝ), (3796920685681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412738561/10000000000 : ℝ)|^2113 ≤ (4447989879673/10000000000000 : ℝ)^1601
        have hw : |(5412738561/10000000000 : ℝ)|=(5412738561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628229029/1250000000 : ℝ)|^2113 ≤ (10083104610051/25000000000000 : ℝ)^1601
        have hw : |(628229029/1250000000 : ℝ)|=(628229029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-239786047/1000000000 : ℝ)|^2113 ≤ (3796920685681/25000000000000 : ℝ)^1601
        have hw : |(-239786047/1000000000 : ℝ)|=(239786047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4307375459/10000000000 : ℝ)*x 0 + (924623617/2500000000 : ℝ)*x 1 + (2506154549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307375459/10000000000 : ℝ)^2113 ≤ (1645144003631/5000000000000 : ℝ)^1601 := by
    have hnat : (4307375459 : ℕ)^2113*5000000000000^1601 ≤ 1645144003631^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307375459 10000000000 1645144003631 5000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924623617/2500000000 : ℝ)^2113 ≤ (26907869081849/100000000000000 : ℝ)^1601 := by
    have hnat : (924623617 : ℕ)^2113*100000000000000^1601 ≤ 26907869081849^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924623617 2500000000 26907869081849 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506154549/5000000000 : ℝ)^2113 ≤ (40189250826837/100000000000000 : ℝ)^1601 := by
    have hnat : (2506154549 : ℕ)^2113*100000000000000^1601 ≤ 40189250826837^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506154549 5000000000 40189250826837 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307375459/10000000000 : ℝ), (924623617/2500000000 : ℝ), (2506154549/5000000000 : ℝ)] ![(1645144003631/5000000000000 : ℝ), (26907869081849/100000000000000 : ℝ), (40189250826837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307375459/10000000000 : ℝ)|^2113 ≤ (1645144003631/5000000000000 : ℝ)^1601
        have hw : |(4307375459/10000000000 : ℝ)|=(4307375459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924623617/2500000000 : ℝ)|^2113 ≤ (26907869081849/100000000000000 : ℝ)^1601
        have hw : |(924623617/2500000000 : ℝ)|=(924623617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506154549/5000000000 : ℝ)|^2113 ≤ (40189250826837/100000000000000 : ℝ)^1601
        have hw : |(2506154549/5000000000 : ℝ)|=(2506154549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052151727/10000000000 : ℝ)*x 0 + (2517127799/5000000000 : ℝ)*x 1 + (5662785097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052151727/10000000000 : ℝ)^2113 ≤ (6183352045987/50000000000000 : ℝ)^1601 := by
    have hnat : (2052151727 : ℕ)^2113*50000000000000^1601 ≤ 6183352045987^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052151727 10000000000 6183352045987 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517127799/5000000000 : ℝ)^2113 ≤ (5052707224909/12500000000000 : ℝ)^1601 := by
    have hnat : (2517127799 : ℕ)^2113*12500000000000^1601 ≤ 5052707224909^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517127799 5000000000 5052707224909 12500000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5662785097/10000000000 : ℝ)^2113 ≤ (47211638091853/100000000000000 : ℝ)^1601 := by
    have hnat : (5662785097 : ℕ)^2113*100000000000000^1601 ≤ 47211638091853^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5662785097 10000000000 47211638091853 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052151727/10000000000 : ℝ), (2517127799/5000000000 : ℝ), (5662785097/10000000000 : ℝ)] ![(6183352045987/50000000000000 : ℝ), (5052707224909/12500000000000 : ℝ), (47211638091853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052151727/10000000000 : ℝ)|^2113 ≤ (6183352045987/50000000000000 : ℝ)^1601
        have hw : |(-2052151727/10000000000 : ℝ)|=(2052151727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517127799/5000000000 : ℝ)|^2113 ≤ (5052707224909/12500000000000 : ℝ)^1601
        have hw : |(2517127799/5000000000 : ℝ)|=(2517127799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5662785097/10000000000 : ℝ)|^2113 ≤ (47211638091853/100000000000000 : ℝ)^1601
        have hw : |(5662785097/10000000000 : ℝ)|=(5662785097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5246296487/10000000000 : ℝ)*x 0 + (-1760907469/10000000000 : ℝ)*x 1 + (1415696373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246296487/10000000000 : ℝ)^2113 ≤ (42683667748181/100000000000000 : ℝ)^1601 := by
    have hnat : (5246296487 : ℕ)^2113*100000000000000^1601 ≤ 42683667748181^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246296487 10000000000 42683667748181 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1760907469/10000000000 : ℝ)^2113 ≤ (2020937958027/20000000000000 : ℝ)^1601 := by
    have hnat : (1760907469 : ℕ)^2113*20000000000000^1601 ≤ 2020937958027^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760907469 10000000000 2020937958027 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1415696373/2500000000 : ℝ)^2113 ≤ (23605821219099/50000000000000 : ℝ)^1601 := by
    have hnat : (1415696373 : ℕ)^2113*50000000000000^1601 ≤ 23605821219099^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415696373 2500000000 23605821219099 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246296487/10000000000 : ℝ), (-1760907469/10000000000 : ℝ), (1415696373/2500000000 : ℝ)] ![(42683667748181/100000000000000 : ℝ), (2020937958027/20000000000000 : ℝ), (23605821219099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246296487/10000000000 : ℝ)|^2113 ≤ (42683667748181/100000000000000 : ℝ)^1601
        have hw : |(5246296487/10000000000 : ℝ)|=(5246296487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1760907469/10000000000 : ℝ)|^2113 ≤ (2020937958027/20000000000000 : ℝ)^1601
        have hw : |(-1760907469/10000000000 : ℝ)|=(1760907469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1415696373/2500000000 : ℝ)|^2113 ≤ (23605821219099/50000000000000 : ℝ)^1601
        have hw : |(1415696373/2500000000 : ℝ)|=(1415696373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2623148203/5000000000 : ℝ)*x 0 + (566278523/1000000000 : ℝ)*x 1 + (-880453983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623148203/5000000000 : ℝ)^2113 ≤ (2667729179901/6250000000000 : ℝ)^1601 := by
    have hnat : (2623148203 : ℕ)^2113*6250000000000^1601 ≤ 2667729179901^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623148203 5000000000 2667729179901 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566278523/1000000000 : ℝ)^2113 ≤ (23605819777653/50000000000000 : ℝ)^1601 := by
    have hnat : (566278523 : ℕ)^2113*50000000000000^1601 ≤ 23605819777653^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566278523 1000000000 23605819777653 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880453983/5000000000 : ℝ)^2113 ≤ (2526173388537/25000000000000 : ℝ)^1601 := by
    have hnat : (880453983 : ℕ)^2113*25000000000000^1601 ≤ 2526173388537^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880453983 5000000000 2526173388537 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623148203/5000000000 : ℝ), (566278523/1000000000 : ℝ), (-880453983/5000000000 : ℝ)] ![(2667729179901/6250000000000 : ℝ), (23605819777653/50000000000000 : ℝ), (2526173388537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623148203/5000000000 : ℝ)|^2113 ≤ (2667729179901/6250000000000 : ℝ)^1601
        have hw : |(2623148203/5000000000 : ℝ)|=(2623148203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566278523/1000000000 : ℝ)|^2113 ≤ (23605819777653/50000000000000 : ℝ)^1601
        have hw : |(566278523/1000000000 : ℝ)|=(566278523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880453983/5000000000 : ℝ)|^2113 ≤ (2526173388537/25000000000000 : ℝ)^1601
        have hw : |(-880453983/5000000000 : ℝ)|=(880453983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s1_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4308711119/10000000000 : ℝ)*x 0 + (999033123/2000000000 : ℝ)*x 1 + (3715962201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308711119/10000000000 : ℝ)^2113 ≤ (32916346326619/100000000000000 : ℝ)^1601 := by
    have hnat : (4308711119 : ℕ)^2113*100000000000000^1601 ≤ 32916346326619^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308711119 10000000000 32916346326619 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999033123/2000000000 : ℝ)^2113 ≤ (40007932574077/100000000000000 : ℝ)^1601 := by
    have hnat : (999033123 : ℕ)^2113*100000000000000^1601 ≤ 40007932574077^1601*2000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999033123 2000000000 40007932574077 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3715962201/10000000000 : ℝ)^2113 ≤ (13537860545971/50000000000000 : ℝ)^1601 := by
    have hnat : (3715962201 : ℕ)^2113*50000000000000^1601 ≤ 13537860545971^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715962201 10000000000 13537860545971 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308711119/10000000000 : ℝ), (999033123/2000000000 : ℝ), (3715962201/10000000000 : ℝ)] ![(32916346326619/100000000000000 : ℝ), (40007932574077/100000000000000 : ℝ), (13537860545971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308711119/10000000000 : ℝ)|^2113 ≤ (32916346326619/100000000000000 : ℝ)^1601
        have hw : |(4308711119/10000000000 : ℝ)|=(4308711119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999033123/2000000000 : ℝ)|^2113 ≤ (40007932574077/100000000000000 : ℝ)^1601
        have hw : |(999033123/2000000000 : ℝ)|=(999033123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3715962201/10000000000 : ℝ)|^2113 ≤ (13537860545971/50000000000000 : ℝ)^1601
        have hw : |(3715962201/10000000000 : ℝ)|=(3715962201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27373/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (157/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19927/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27373/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27373/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27373/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27373/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27373/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27373/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (443/50000 : ℝ) ^ (8451/2048 : ℝ) ≤ (338966995481/100000000000000000000 : ℝ) := by
    have hpowers : (443/50000 : ℝ)^8451 ≤ (338966995481/100000000000000000000 : ℝ)^2048 := by
      have hnat : (443 : ℕ)^8451*100000000000000000000^2048 ≤ 338966995481^2048*50000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 50000 338966995481 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/50000 : ℝ)) (X := (338966995481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27373/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (476574339404301577/100000000000000000000 : ℝ) := by
    have hpowers : (27373/100000 : ℝ)^8451 ≤ (476574339404301577/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27373 : ℕ)^8451*100000000000000000000^2048 ≤ 476574339404301577^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27373 100000 476574339404301577 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27373/100000 : ℝ)) (X := (476574339404301577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000338966995481/50000000000000000000 : ℝ) ≤ (1000000001642893/1000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50000000338966995481/50000000000000000000 : ℝ)^2048 ≤ (1000000001642893/1000000000000000 : ℝ)^8451 := by
      have hnat : (50000000338966995481 : ℕ)^2048*1000000000000000^8451 ≤ 1000000001642893^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000338966995481 50000000000000000000 1000000001642893 1000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000001642893/1000000000000000 : ℝ)) (X := (50000000338966995481/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50238287339185648529/50000000000000000000 : ℝ) ≤ (2502882107792199/2500000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50238287339185648529/50000000000000000000 : ℝ)^2048 ≤ (2502882107792199/2500000000000000 : ℝ)^8451 := by
      have hnat : (50238287339185648529 : ℕ)^2048*2500000000000000^8451 ≤ 2502882107792199^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50238287339185648529 50000000000000000000 2502882107792199 2500000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502882107792199/2500000000000000 : ℝ)) (X := (50238287339185648529/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50476574339404301577/50000000000000000000 : ℝ) ≤ (5011528422954331/5000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50476574339404301577/50000000000000000000 : ℝ)^2048 ≤ (5011528422954331/5000000000000000 : ℝ)^8451 := by
      have hnat : (50476574339404301577 : ℕ)^2048*5000000000000000^8451 ≤ 5011528422954331^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50476574339404301577 50000000000000000000 5011528422954331 5000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011528422954331/5000000000000000 : ℝ)) (X := (50476574339404301577/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(338966995481/100000000000000000000 : ℝ) ≤ ((132424786042117013179/132435000000000000000 : ℝ)+2*(5764207369933/1324350000000000 : ℝ)*(443/50000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (132424786042117013179/132435000000000000000 : ℝ)+2*(5764207369933/1324350000000000 : ℝ)*(443/50000 : ℝ)=(1000000001642893/1000000000000000 : ℝ) by norm_num, show 1+2*(338966995481/100000000000000000000 : ℝ)=(50000000338966995481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(476574339404301577/100000000000000000000 : ℝ)+(338966995481/100000000000000000000 : ℝ) ≤ ((132424786042117013179/132435000000000000000 : ℝ)+(5764207369933/1324350000000000 : ℝ)*((27373/100000 : ℝ)+(443/50000 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (132424786042117013179/132435000000000000000 : ℝ)+(5764207369933/1324350000000000 : ℝ)*((27373/100000 : ℝ)+(443/50000 : ℝ))=(2502882107792199/2500000000000000 : ℝ) by norm_num, show 1+(476574339404301577/100000000000000000000 : ℝ)+(338966995481/100000000000000000000 : ℝ)=(50238287339185648529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(476574339404301577/100000000000000000000 : ℝ) ≤ ((132424786042117013179/132435000000000000000 : ℝ)+2*(5764207369933/1324350000000000 : ℝ)*(27373/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (132424786042117013179/132435000000000000000 : ℝ)+2*(5764207369933/1324350000000000 : ℝ)*(27373/100000 : ℝ)=(5011528422954331/5000000000000000 : ℝ) by norm_num, show 1+2*(476574339404301577/100000000000000000000 : ℝ)=(50476574339404301577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132424786042117013179/132435000000000000000 : ℝ)*(X 1 0+X 2 0)+(5764207369933/1324350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (443/50000 : ℝ)) (hi := (27373/100000 : ℝ)) (c := (132424786042117013179/132435000000000000000 : ℝ)) (alpha := (5764207369933/1324350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132424786042117013179/132435000000000000000 : ℝ)*(X 0 1+X 2 1)+(5764207369933/1324350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (443/50000 : ℝ)) (hi := (27373/100000 : ℝ)) (c := (132424786042117013179/132435000000000000000 : ℝ)) (alpha := (5764207369933/1324350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132424786042117013179/132435000000000000000 : ℝ)*(X 0 2+X 1 2)+(5764207369933/1324350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (443/50000 : ℝ)) (hi := (27373/100000 : ℝ)) (c := (132424786042117013179/132435000000000000000 : ℝ)) (alpha := (5764207369933/1324350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2051495321/10000000000 : ℝ)*X 0 0+(1417841921/2500000000 : ℝ)*X 0 1+(2512916077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706369201/5000000000 : ℝ)*X 1 0+(-2397860551/10000000000 : ℝ)*X 1 1+(5025832331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412738561/10000000000 : ℝ)*X 2 0+(628229029/1250000000 : ℝ)*X 2 1+(-239786047/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307375459/10000000000 : ℝ)*X 0 0+(924623617/2500000000 : ℝ)*X 0 1+(2506154549/5000000000 : ℝ)*X 0 2+(4307375459/10000000000 : ℝ)*X 1 0+(924623617/2500000000 : ℝ)*X 1 1+(2506154549/5000000000 : ℝ)*X 1 2+(4307375459/10000000000 : ℝ)*X 2 0+(924623617/2500000000 : ℝ)*X 2 1+(2506154549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2052151727/10000000000 : ℝ)*X 0 0+(2517127799/5000000000 : ℝ)*X 0 1+(5662785097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246296487/10000000000 : ℝ)*X 1 0+(-1760907469/10000000000 : ℝ)*X 1 1+(1415696373/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2623148203/5000000000 : ℝ)*X 2 0+(566278523/1000000000 : ℝ)*X 2 1+(-880453983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308711119/10000000000 : ℝ)*X 0 0+(999033123/2000000000 : ℝ)*X 0 1+(3715962201/10000000000 : ℝ)*X 0 2+(4308711119/10000000000 : ℝ)*X 1 0+(999033123/2000000000 : ℝ)*X 1 1+(3715962201/10000000000 : ℝ)*X 1 2+(4308711119/10000000000 : ℝ)*X 2 0+(999033123/2000000000 : ℝ)*X 2 1+(3715962201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83435305188527251998632437/61312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1083369/25000000000000 : ℝ)*(base1) + (354083247/100000000000000 : ℝ)*(base19) + (19979423/5000000000000 : ℝ)*(base23) + (31607273/100000000000000 : ℝ)*(upper3) + (73958163/100000000000000 : ℝ)*(upper5) + (288781393913427/25000000000000 : ℝ)*(major0) + (288781393913427/25000000000000 : ℝ)*(major1) + (288781393913427/25000000000000 : ℝ)*(major2) + (1549103462421607/100000000000000 : ℝ)*(sp0) + (309821153841663/20000000000000 : ℝ)*(sp1) + (774552861851551/50000000000000 : ℝ)*(sp2) + (380571868425889/50000000000000 : ℝ)*(sp3) + (333150429/12500000000000 : ℝ)*(sp4) + (155183739/12500000000000 : ℝ)*(sp7) + (380572491327583/50000000000000 : ℝ)*(f.failure) + (774553061645781/50000000000000 : ℝ)*(f.sum) + (5198959879121/44145000000000000000000000000 : ℝ)*base65 + (1904334823347115189/1103625000000000000000000000000000 : ℝ)*base68 + (8263506423405865189/1103625000000000000000000000000000 : ℝ)*base70 + (842830872851884811/1103625000000000000000000000000000 : ℝ)*base71 + (72832567632379/44145000000000000000000000000 : ℝ)*base74 + (3223502545781740189/1103625000000000000000000000000000 : ℝ)*base76 + (5066951596130884811/1103625000000000000000000000000000 : ℝ)*base77 + (527036361229615189/1103625000000000000000000000000000 : ℝ)*base80 + (18365933565559/2759062500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1961469/500000000000000000000 : ℝ)*base90 + (1961469/500000000000000000000 : ℝ)*base92 + (1961469/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88333107223609184564929/22072500000000000000000000000 : ℝ) := by norm_num
    linear_combination (713338173/100000000000000 : ℝ)*(base19) + (658399909/100000000000000 : ℝ)*(base23) + (541423/50000000000000 : ℝ)*(upper2) + (58231111/50000000000000 : ℝ)*(upper3) + (82996811/100000000000000 : ℝ)*(upper5) + (148296962857909/12500000000000 : ℝ)*(major0) + (148296962857909/12500000000000 : ℝ)*(major1) + (148296962857909/12500000000000 : ℝ)*(major2) + (200778441/5000000000000 : ℝ)*(sp1) + (748278319/25000000000000 : ℝ)*(sp2) + (795507347550779/50000000000000 : ℝ)*(sp4) + (318201993238913/20000000000000 : ℝ)*(sp5) + (795505521794187/50000000000000 : ℝ)*(sp6) + (195434144306637/25000000000000 : ℝ)*(sp7) + (195434144306637/25000000000000 : ℝ)*(f.failure) + (795507347550779/50000000000000 : ℝ)*(f.sum) + (221961089733979/66217500000000000000000000000 : ℝ)*base66 + (1927300770439082711/1655437500000000000000000000000000 : ℝ)*base67 + (3521611952589707711/1655437500000000000000000000000000 : ℝ)*base69 + (243659080154020211/1655437500000000000000000000000000 : ℝ)*base71 + (157872436993027/132435000000000000000000000000 : ℝ)*base73 + (3926018059937667289/1655437500000000000000000000000000 : ℝ)*base76 + (15151911134908167289/1655437500000000000000000000000000 : ℝ)*base78 + (7169007746386917289/1655437500000000000000000000000000 : ℝ)*base80 + (57608744144489/16554375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (745991/250000000000000000000 : ℝ)*base90 + (745991/250000000000000000000 : ℝ)*base92 + (745991/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1259_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27373/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (157/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19927/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1259_s2_0 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049349257/5000000000 : ℝ)*x 0 + (219596659/400000000 : ℝ)*x 1 + (5177164729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049349257/5000000000 : ℝ)^2113 ≤ (12738245008989/100000000000000 : ℝ)^1601 := by
    have hnat : (1049349257 : ℕ)^2113*100000000000000^1601 ≤ 12738245008989^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049349257 5000000000 12738245008989 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219596659/400000000 : ℝ)^2113 ≤ (45318844408943/100000000000000 : ℝ)^1601 := by
    have hnat : (219596659 : ℕ)^2113*100000000000000^1601 ≤ 45318844408943^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219596659 400000000 45318844408943 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177164729/10000000000 : ℝ)^2113 ≤ (8388582113973/20000000000000 : ℝ)^1601 := by
    have hnat : (5177164729 : ℕ)^2113*20000000000000^1601 ≤ 8388582113973^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177164729 10000000000 8388582113973 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049349257/5000000000 : ℝ), (219596659/400000000 : ℝ), (5177164729/10000000000 : ℝ)] ![(12738245008989/100000000000000 : ℝ), (45318844408943/100000000000000 : ℝ), (8388582113973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049349257/5000000000 : ℝ)|^2113 ≤ (12738245008989/100000000000000 : ℝ)^1601
        have hw : |(-1049349257/5000000000 : ℝ)|=(1049349257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219596659/400000000 : ℝ)|^2113 ≤ (45318844408943/100000000000000 : ℝ)^1601
        have hw : |(219596659/400000000 : ℝ)|=(219596659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177164729/10000000000 : ℝ)|^2113 ≤ (8388582113973/20000000000000 : ℝ)^1601
        have hw : |(5177164729/10000000000 : ℝ)|=(5177164729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_1 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684499301/5000000000 : ℝ)*x 0 + (-565151657/2500000000 : ℝ)*x 1 + (5177164889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684499301/5000000000 : ℝ)^2113 ≤ (11001531339081/25000000000000 : ℝ)^1601 := by
    have hnat : (2684499301 : ℕ)^2113*25000000000000^1601 ≤ 11001531339081^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684499301 5000000000 11001531339081 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565151657/2500000000 : ℝ)^2113 ≤ (14050962342367/100000000000000 : ℝ)^1601 := by
    have hnat : (565151657 : ℕ)^2113*100000000000000^1601 ≤ 14050962342367^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565151657 2500000000 14050962342367 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177164889/10000000000 : ℝ)^2113 ≤ (41942912280647/100000000000000 : ℝ)^1601 := by
    have hnat : (5177164889 : ℕ)^2113*100000000000000^1601 ≤ 41942912280647^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177164889 10000000000 41942912280647 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684499301/5000000000 : ℝ), (-565151657/2500000000 : ℝ), (5177164889/10000000000 : ℝ)] ![(11001531339081/25000000000000 : ℝ), (14050962342367/100000000000000 : ℝ), (41942912280647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684499301/5000000000 : ℝ)|^2113 ≤ (11001531339081/25000000000000 : ℝ)^1601
        have hw : |(2684499301/5000000000 : ℝ)|=(2684499301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-565151657/2500000000 : ℝ)|^2113 ≤ (14050962342367/100000000000000 : ℝ)^1601
        have hw : |(-565151657/2500000000 : ℝ)|=(565151657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177164889/10000000000 : ℝ)|^2113 ≤ (41942912280647/100000000000000 : ℝ)^1601
        have hw : |(5177164889/10000000000 : ℝ)|=(5177164889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_2 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368998519/10000000000 : ℝ)*x 0 + (207086597/400000000 : ℝ)*x 1 + (-565151673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368998519/10000000000 : ℝ)^2113 ≤ (44006124458469/100000000000000 : ℝ)^1601 := by
    have hnat : (5368998519 : ℕ)^2113*100000000000000^1601 ≤ 44006124458469^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368998519 10000000000 44006124458469 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207086597/400000000 : ℝ)^2113 ≤ (41942912665573/100000000000000 : ℝ)^1601 := by
    have hnat : (207086597 : ℕ)^2113*100000000000000^1601 ≤ 41942912665573^1601*400000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207086597 400000000 41942912665573 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565151673/2500000000 : ℝ)^2113 ≤ (14050962867379/100000000000000 : ℝ)^1601 := by
    have hnat : (565151673 : ℕ)^2113*100000000000000^1601 ≤ 14050962867379^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565151673 2500000000 14050962867379 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368998519/10000000000 : ℝ), (207086597/400000000 : ℝ), (-565151673/2500000000 : ℝ)] ![(44006124458469/100000000000000 : ℝ), (41942912665573/100000000000000 : ℝ), (14050962867379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368998519/10000000000 : ℝ)|^2113 ≤ (44006124458469/100000000000000 : ℝ)^1601
        have hw : |(5368998519/10000000000 : ℝ)|=(5368998519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207086597/400000000 : ℝ)|^2113 ≤ (41942912665573/100000000000000 : ℝ)^1601
        have hw : |(207086597/400000000 : ℝ)|=(207086597/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565151673/2500000000 : ℝ)|^2113 ≤ (14050962867379/100000000000000 : ℝ)^1601
        have hw : |(-565151673/2500000000 : ℝ)|=(565151673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_3 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2170007187/5000000000 : ℝ)*x 0 + (4033013257/10000000000 : ℝ)*x 1 + (4669534937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170007187/5000000000 : ℝ)^2113 ≤ (33232330481661/100000000000000 : ℝ)^1601 := by
    have hnat : (2170007187 : ℕ)^2113*100000000000000^1601 ≤ 33232330481661^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170007187 5000000000 33232330481661 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4033013257/10000000000 : ℝ)^2113 ≤ (1885341292987/6250000000000 : ℝ)^1601 := by
    have hnat : (4033013257 : ℕ)^2113*6250000000000^1601 ≤ 1885341292987^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033013257 10000000000 1885341292987 6250000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4669534937/10000000000 : ℝ)^2113 ≤ (18301104408967/50000000000000 : ℝ)^1601 := by
    have hnat : (4669534937 : ℕ)^2113*50000000000000^1601 ≤ 18301104408967^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669534937 10000000000 18301104408967 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170007187/5000000000 : ℝ), (4033013257/10000000000 : ℝ), (4669534937/10000000000 : ℝ)] ![(33232330481661/100000000000000 : ℝ), (1885341292987/6250000000000 : ℝ), (18301104408967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170007187/5000000000 : ℝ)|^2113 ≤ (33232330481661/100000000000000 : ℝ)^1601
        have hw : |(2170007187/5000000000 : ℝ)|=(2170007187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4033013257/10000000000 : ℝ)|^2113 ≤ (1885341292987/6250000000000 : ℝ)^1601
        have hw : |(4033013257/10000000000 : ℝ)|=(4033013257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4669534937/10000000000 : ℝ)|^2113 ≤ (18301104408967/50000000000000 : ℝ)^1601
        have hw : |(4669534937/10000000000 : ℝ)|=(4669534937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_4 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098773463/10000000000 : ℝ)*x 0 + (5179151773/10000000000 : ℝ)*x 1 + (1371977753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098773463/10000000000 : ℝ)^2113 ≤ (3184711350639/25000000000000 : ℝ)^1601 := by
    have hnat : (2098773463 : ℕ)^2113*25000000000000^1601 ≤ 3184711350639^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098773463 10000000000 3184711350639 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179151773/10000000000 : ℝ)^2113 ≤ (41964158120839/100000000000000 : ℝ)^1601 := by
    have hnat : (5179151773 : ℕ)^2113*100000000000000^1601 ≤ 41964158120839^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179151773 10000000000 41964158120839 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371977753/2500000000 : ℝ)^2113 ≤ (1811879858669/4000000000000 : ℝ)^1601 := by
    have hnat : (1371977753 : ℕ)^2113*4000000000000^1601 ≤ 1811879858669^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371977753 2500000000 1811879858669 4000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098773463/10000000000 : ℝ), (5179151773/10000000000 : ℝ), (1371977753/2500000000 : ℝ)] ![(3184711350639/25000000000000 : ℝ), (41964158120839/100000000000000 : ℝ), (1811879858669/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098773463/10000000000 : ℝ)|^2113 ≤ (3184711350639/25000000000000 : ℝ)^1601
        have hw : |(-2098773463/10000000000 : ℝ)|=(2098773463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179151773/10000000000 : ℝ)|^2113 ≤ (41964158120839/100000000000000 : ℝ)^1601
        have hw : |(5179151773/10000000000 : ℝ)|=(5179151773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371977753/2500000000 : ℝ)|^2113 ≤ (1811879858669/4000000000000 : ℝ)^1601
        have hw : |(1371977753/2500000000 : ℝ)|=(1371977753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_5 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289046199/10000000000 : ℝ)*x 0 + (-1949860243/10000000000 : ℝ)*x 1 + (342994441/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289046199/10000000000 : ℝ)^2113 ≤ (21571652233307/50000000000000 : ℝ)^1601 := by
    have hnat : (5289046199 : ℕ)^2113*50000000000000^1601 ≤ 21571652233307^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289046199 10000000000 21571652233307 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949860243/10000000000 : ℝ)^2113 ≤ (2311939715191/20000000000000 : ℝ)^1601 := by
    have hnat : (1949860243 : ℕ)^2113*20000000000000^1601 ≤ 2311939715191^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949860243 10000000000 2311939715191 20000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342994441/625000000 : ℝ)^2113 ≤ (22648498473021/50000000000000 : ℝ)^1601 := by
    have hnat : (342994441 : ℕ)^2113*50000000000000^1601 ≤ 22648498473021^1601*625000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342994441 625000000 22648498473021 50000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289046199/10000000000 : ℝ), (-1949860243/10000000000 : ℝ), (342994441/625000000 : ℝ)] ![(21571652233307/50000000000000 : ℝ), (2311939715191/20000000000000 : ℝ), (22648498473021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289046199/10000000000 : ℝ)|^2113 ≤ (21571652233307/50000000000000 : ℝ)^1601
        have hw : |(5289046199/10000000000 : ℝ)|=(5289046199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949860243/10000000000 : ℝ)|^2113 ≤ (2311939715191/20000000000000 : ℝ)^1601
        have hw : |(-1949860243/10000000000 : ℝ)|=(1949860243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342994441/625000000 : ℝ)|^2113 ≤ (22648498473021/50000000000000 : ℝ)^1601
        have hw : |(342994441/625000000 : ℝ)|=(342994441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_6 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289046331/10000000000 : ℝ)*x 0 + (1371977791/2500000000 : ℝ)*x 1 + (-194985991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289046331/10000000000 : ℝ)^2113 ≤ (10785826471923/25000000000000 : ℝ)^1601 := by
    have hnat : (5289046331 : ℕ)^2113*25000000000000^1601 ≤ 10785826471923^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289046331 10000000000 10785826471923 25000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371977791/2500000000 : ℝ)^2113 ≤ (45296998122549/100000000000000 : ℝ)^1601 := by
    have hnat : (1371977791 : ℕ)^2113*100000000000000^1601 ≤ 45296998122549^1601*2500000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371977791 2500000000 45296998122549 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194985991/1000000000 : ℝ)^2113 ≤ (11559695970429/100000000000000 : ℝ)^1601 := by
    have hnat : (194985991 : ℕ)^2113*100000000000000^1601 ≤ 11559695970429^1601*1000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194985991 1000000000 11559695970429 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289046331/10000000000 : ℝ), (1371977791/2500000000 : ℝ), (-194985991/1000000000 : ℝ)] ![(10785826471923/25000000000000 : ℝ), (45296998122549/100000000000000 : ℝ), (11559695970429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289046331/10000000000 : ℝ)|^2113 ≤ (10785826471923/25000000000000 : ℝ)^1601
        have hw : |(5289046331/10000000000 : ℝ)|=(5289046331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371977791/2500000000 : ℝ)|^2113 ≤ (45296998122549/100000000000000 : ℝ)^1601
        have hw : |(1371977791/2500000000 : ℝ)|=(1371977791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194985991/1000000000 : ℝ)|^2113 ≤ (11559695970429/100000000000000 : ℝ)^1601
        have hw : |(-194985991/1000000000 : ℝ)|=(194985991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1259_s2_7 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2170083227/5000000000 : ℝ)*x 0 + (46654913/100000000 : ℝ)*x 1 + (4037093973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170083227/5000000000 : ℝ)^2113 ≤ (33233867405449/100000000000000 : ℝ)^1601 := by
    have hnat : (2170083227 : ℕ)^2113*100000000000000^1601 ≤ 33233867405449^1601*5000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170083227 5000000000 33233867405449 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46654913/100000000 : ℝ)^2113 ≤ (36560382094897/100000000000000 : ℝ)^1601 := by
    have hnat : (46654913 : ℕ)^2113*100000000000000^1601 ≤ 36560382094897^1601*100000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46654913 100000000 36560382094897 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4037093973/10000000000 : ℝ)^2113 ≤ (30205750485973/100000000000000 : ℝ)^1601 := by
    have hnat : (4037093973 : ℕ)^2113*100000000000000^1601 ≤ 30205750485973^1601*10000000000^2113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037093973 10000000000 30205750485973 100000000000000 2113 1601 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2113/512 : ℝ)) 2113 1601 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170083227/5000000000 : ℝ), (46654913/100000000 : ℝ), (4037093973/10000000000 : ℝ)] ![(33233867405449/100000000000000 : ℝ), (36560382094897/100000000000000 : ℝ), (30205750485973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170083227/5000000000 : ℝ)|^2113 ≤ (33233867405449/100000000000000 : ℝ)^1601
        have hw : |(2170083227/5000000000 : ℝ)|=(2170083227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46654913/100000000 : ℝ)|^2113 ≤ (36560382094897/100000000000000 : ℝ)^1601
        have hw : |(46654913/100000000 : ℝ)|=(46654913/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4037093973/10000000000 : ℝ)|^2113 ≤ (30205750485973/100000000000000 : ℝ)^1601
        have hw : |(4037093973/10000000000 : ℝ)|=(4037093973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1259_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19927/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (157/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (299/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16179/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19927/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (157/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19927/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (157/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19927/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (157/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19927/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (157/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19927/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (157/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19927/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (157/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (157/2500 : ℝ) ^ (8451/2048 : ℝ) ≤ (548015362787981/50000000000000000000 : ℝ) := by
    have hpowers : (157/2500 : ℝ)^8451 ≤ (548015362787981/50000000000000000000 : ℝ)^2048 := by
      have hnat : (157 : ℕ)^8451*50000000000000000000^2048 ≤ 548015362787981^2048*2500^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        157 2500 548015362787981 50000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (157/2500 : ℝ)) (X := (548015362787981/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19927/100000 : ℝ) ^ (8451/2048 : ℝ) ≤ (128579494840475579/100000000000000000000 : ℝ) := by
    have hpowers : (19927/100000 : ℝ)^8451 ≤ (128579494840475579/100000000000000000000 : ℝ)^2048 := by
      have hnat : (19927 : ℕ)^8451*100000000000000000000^2048 ≤ 128579494840475579^2048*100000^8451 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19927 100000 128579494840475579 100000000000000000000 8451 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19927/100000 : ℝ)) (X := (128579494840475579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000548015362787981/25000000000000000000 : ℝ) ≤ (10000053121578181/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (25000548015362787981/25000000000000000000 : ℝ)^2048 ≤ (10000053121578181/10000000000000000 : ℝ)^8451 := by
      have hnat : (25000548015362787981 : ℕ)^2048*10000000000000000^8451 ≤ 10000053121578181^8451*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000548015362787981 25000000000000000000 10000053121578181 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000053121578181/10000000000000000 : ℝ)) (X := (25000548015362787981/25000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100129675525566051541/100000000000000000000 : ℝ) ≤ (10003140990547637/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (100129675525566051541/100000000000000000000 : ℝ)^2048 ≤ (10003140990547637/10000000000000000 : ℝ)^8451 := by
      have hnat : (100129675525566051541 : ℕ)^2048*10000000000000000^8451 ≤ 10003140990547637^8451*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100129675525566051541 100000000000000000000 10003140990547637 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003140990547637/10000000000000000 : ℝ)) (X := (100129675525566051541/100000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50128579494840475579/50000000000000000000 : ℝ) ≤ (10006228859517093/10000000000000000 : ℝ) ^ (8451/2048 : ℝ) := by
    have hpowers : (50128579494840475579/50000000000000000000 : ℝ)^2048 ≤ (10006228859517093/10000000000000000 : ℝ)^8451 := by
      have hnat : (50128579494840475579 : ℕ)^2048*10000000000000000^8451 ≤ 10006228859517093^8451*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50128579494840475579 50000000000000000000 10006228859517093 10000000000000000 2048 8451 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006228859517093/10000000000000000 : ℝ)) (X := (50128579494840475579/50000000000000000000 : ℝ)) (by norm_num) 8451 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(548015362787981/50000000000000000000 : ℝ) ≤ ((136431941315921068747/136470000000000000000 : ℝ)+2*(192991810591/85293750000000 : ℝ)*(157/2500 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (136431941315921068747/136470000000000000000 : ℝ)+2*(192991810591/85293750000000 : ℝ)*(157/2500 : ℝ)=(10000053121578181/10000000000000000 : ℝ) by norm_num, show 1+2*(548015362787981/50000000000000000000 : ℝ)=(25000548015362787981/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(128579494840475579/100000000000000000000 : ℝ)+(548015362787981/50000000000000000000 : ℝ) ≤ ((136431941315921068747/136470000000000000000 : ℝ)+(192991810591/85293750000000 : ℝ)*((19927/100000 : ℝ)+(157/2500 : ℝ)))^(8451/2048 : ℝ) := by
    rw [show (136431941315921068747/136470000000000000000 : ℝ)+(192991810591/85293750000000 : ℝ)*((19927/100000 : ℝ)+(157/2500 : ℝ))=(10003140990547637/10000000000000000 : ℝ) by norm_num, show 1+(128579494840475579/100000000000000000000 : ℝ)+(548015362787981/50000000000000000000 : ℝ)=(100129675525566051541/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(128579494840475579/100000000000000000000 : ℝ) ≤ ((136431941315921068747/136470000000000000000 : ℝ)+2*(192991810591/85293750000000 : ℝ)*(19927/100000 : ℝ))^(8451/2048 : ℝ) := by
    rw [show (136431941315921068747/136470000000000000000 : ℝ)+2*(192991810591/85293750000000 : ℝ)*(19927/100000 : ℝ)=(10006228859517093/10000000000000000 : ℝ) by norm_num, show 1+2*(128579494840475579/100000000000000000000 : ℝ)=(50128579494840475579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (136431941315921068747/136470000000000000000 : ℝ)*(X 1 0+X 2 0)+(192991810591/85293750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (157/2500 : ℝ)) (hi := (19927/100000 : ℝ)) (c := (136431941315921068747/136470000000000000000 : ℝ)) (alpha := (192991810591/85293750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (136431941315921068747/136470000000000000000 : ℝ)*(X 0 1+X 2 1)+(192991810591/85293750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (157/2500 : ℝ)) (hi := (19927/100000 : ℝ)) (c := (136431941315921068747/136470000000000000000 : ℝ)) (alpha := (192991810591/85293750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (136431941315921068747/136470000000000000000 : ℝ)*(X 0 2+X 1 2)+(192991810591/85293750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8451/2048 : ℝ)) (lo := (157/2500 : ℝ)) (hi := (19927/100000 : ℝ)) (c := (136431941315921068747/136470000000000000000 : ℝ)) (alpha := (192991810591/85293750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049349257/5000000000 : ℝ)*X 0 0+(219596659/400000000 : ℝ)*X 0 1+(5177164729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684499301/5000000000 : ℝ)*X 1 0+(-565151657/2500000000 : ℝ)*X 1 1+(5177164889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368998519/10000000000 : ℝ)*X 2 0+(207086597/400000000 : ℝ)*X 2 1+(-565151673/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170007187/5000000000 : ℝ)*X 0 0+(4033013257/10000000000 : ℝ)*X 0 1+(4669534937/10000000000 : ℝ)*X 0 2+(2170007187/5000000000 : ℝ)*X 1 0+(4033013257/10000000000 : ℝ)*X 1 1+(4669534937/10000000000 : ℝ)*X 1 2+(2170007187/5000000000 : ℝ)*X 2 0+(4033013257/10000000000 : ℝ)*X 2 1+(4669534937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2098773463/10000000000 : ℝ)*X 0 0+(5179151773/10000000000 : ℝ)*X 0 1+(1371977753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289046199/10000000000 : ℝ)*X 1 0+(-1949860243/10000000000 : ℝ)*X 1 1+(342994441/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289046331/10000000000 : ℝ)*X 2 0+(1371977791/2500000000 : ℝ)*X 2 1+(-194985991/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170083227/5000000000 : ℝ)*X 0 0+(46654913/100000000 : ℝ)*X 0 1+(4037093973/10000000000 : ℝ)*X 0 2+(2170083227/5000000000 : ℝ)*X 1 0+(46654913/100000000 : ℝ)*X 1 1+(4037093973/10000000000 : ℝ)*X 1 2+(2170083227/5000000000 : ℝ)*X 2 0+(46654913/100000000 : ℝ)*X 2 1+(4037093973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1259_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115582106825792031008763/22745000000000000000000000000 : ℝ) := by norm_num
    linear_combination (217752747/25000000000000 : ℝ)*(base19) + (97447673/12500000000000 : ℝ)*(base23) + (22549739/100000000000000 : ℝ)*(lower2) + (73509223/50000000000000 : ℝ)*(upper3) + (28362699/50000000000000 : ℝ)*(upper5) + (2384247649927419/100000000000000 : ℝ)*(major0) + (2384247649927419/100000000000000 : ℝ)*(major1) + (2384247649927419/100000000000000 : ℝ)*(major2) + (319743634143081/10000000000000 : ℝ)*(sp0) + (1598722951924583/50000000000000 : ℝ)*(sp1) + (319744599527877/10000000000000 : ℝ)*(sp2) + (196380369478789/12500000000000 : ℝ)*(sp3) + (10433429343/100000000000000 : ℝ)*(sp4) + (5399776063/100000000000000 : ℝ)*(sp7) + (196381044450797/12500000000000 : ℝ)*(f.failure) + (1598723387430077/50000000000000 : ℝ)*(f.sum) + (2747577367643/22745000000000000000000000000 : ℝ)*base65 + (29580067030444891331/4549000000000000000000000000000000 : ℝ)*base67 + (36866490210920891331/4549000000000000000000000000000000 : ℝ)*base69 + (20112264040743891331/4549000000000000000000000000000000 : ℝ)*base71 + (34426988291217/5686250000000000000000000000 : ℝ)*base73 + (39864253886511108669/4549000000000000000000000000000000 : ℝ)*base76 + (18323491109458108669/4549000000000000000000000000000000 : ℝ)*base78 + (36293421339744108669/4549000000000000000000000000000000 : ℝ)*base80 + (158048261535453/22745000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (297129/125000000000000000000 : ℝ)*base89 + (297129/125000000000000000000 : ℝ)*base91 + (297129/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1088233270183934187096552587/227450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67684927/5000000000000 : ℝ)*(base19) + (1630289651/100000000000000 : ℝ)*(base23) + (5267253/10000000000000 : ℝ)*(upper2) + (195779541/100000000000000 : ℝ)*(upper3) + (226141/250000000000 : ℝ)*(upper5) + (241505921188721/10000000000000 : ℝ)*(major0) + (241505921188721/10000000000000 : ℝ)*(major1) + (241505921188721/10000000000000 : ℝ)*(major2) + (2762845703/20000000000000 : ℝ)*(sp1) + (2017632783/10000000000000 : ℝ)*(sp2) + (3238767297187269/100000000000000 : ℝ)*(sp4) + (1619376064630107/50000000000000 : ℝ)*(sp5) + (809686372642447/25000000000000 : ℝ)*(sp6) + (795675483551999/50000000000000 : ℝ)*(sp7) + (795675483551999/50000000000000 : ℝ)*(f.failure) + (3238767297187269/100000000000000 : ℝ)*(f.sum) + (50904528693937/13647000000000000000000000000 : ℝ)*base65 + (5404114504824297413/1364700000000000000000000000000000 : ℝ)*base68 + (2314062419734202587/1364700000000000000000000000000000 : ℝ)*base69 + (1029091516127997413/1364700000000000000000000000000000 : ℝ)*base72 + (1419411722107/6823500000000000000000000000 : ℝ)*base74 + (5629623723103497413/1364700000000000000000000000000000 : ℝ)*base76 + (6930972974136602587/1364700000000000000000000000000000 : ℝ)*base77 + (6645033546835797413/1364700000000000000000000000000000 : ℝ)*base80 + (15233895215147/6823500000000000000000000000 : ℝ)*base81 + (4487843/500000000000000000000 : ℝ)*base89 + (4487843/500000000000000000000 : ℝ)*base91 + (4487843/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1259_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19927/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (157/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1259_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1259_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1259_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1259_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1259_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15176157/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (299/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16179/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1259_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
