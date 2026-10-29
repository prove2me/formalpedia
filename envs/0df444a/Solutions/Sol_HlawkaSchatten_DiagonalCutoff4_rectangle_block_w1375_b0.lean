-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1375_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:21:28.893472+00:00
-- url     : https://prove2.me/submissions/3f6cdbcf-97ba-437e-9d4e-db4b7fb9c887

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
theorem support_rectangle_w1375_s0_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789797307/10000000000 : ℝ)*x 0 + (299139283/500000000 : ℝ)*x 1 + (192748851/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789797307/10000000000 : ℝ)^4335 ≤ (10512763891391/100000000000000 : ℝ)^3311 := by
    have hnat : (1789797307 : ℕ)^4335*100000000000000^3311 ≤ 10512763891391^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789797307 10000000000 10512763891391 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299139283/500000000 : ℝ)^4335 ≤ (12759859934951/25000000000000 : ℝ)^3311 := by
    have hnat : (299139283 : ℕ)^4335*25000000000000^3311 ≤ 12759859934951^3311*500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299139283 500000000 12759859934951 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192748851/400000000 : ℝ)^4335 ≤ (1201493635981/3125000000000 : ℝ)^3311 := by
    have hnat : (192748851 : ℕ)^4335*3125000000000^3311 ≤ 1201493635981^3311*400000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192748851 400000000 1201493635981 3125000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789797307/10000000000 : ℝ), (299139283/500000000 : ℝ), (192748851/400000000 : ℝ)] ![(10512763891391/100000000000000 : ℝ), (12759859934951/25000000000000 : ℝ), (1201493635981/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789797307/10000000000 : ℝ)|^4335 ≤ (10512763891391/100000000000000 : ℝ)^3311
        have hw : |(-1789797307/10000000000 : ℝ)|=(1789797307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(299139283/500000000 : ℝ)|^4335 ≤ (12759859934951/25000000000000 : ℝ)^3311
        have hw : |(299139283/500000000 : ℝ)|=(299139283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192748851/400000000 : ℝ)|^4335 ≤ (1201493635981/3125000000000 : ℝ)^3311
        have hw : |(192748851/400000000 : ℝ)|=(192748851/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2749060449/5000000000 : ℝ)*x 0 + (-2449875071/10000000000 : ℝ)*x 1 + (4818721893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749060449/5000000000 : ℝ)^4335 ≤ (45695118270773/100000000000000 : ℝ)^3311 := by
    have hnat : (2749060449 : ℕ)^4335*100000000000000^3311 ≤ 45695118270773^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749060449 5000000000 45695118270773 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2449875071/10000000000 : ℝ)^4335 ≤ (3171415781937/20000000000000 : ℝ)^3311 := by
    have hnat : (2449875071 : ℕ)^4335*20000000000000^3311 ≤ 3171415781937^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449875071 10000000000 3171415781937 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4818721893/10000000000 : ℝ)^4335 ≤ (38447802807311/100000000000000 : ℝ)^3311 := by
    have hnat : (4818721893 : ℕ)^4335*100000000000000^3311 ≤ 38447802807311^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4818721893 10000000000 38447802807311 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749060449/5000000000 : ℝ), (-2449875071/10000000000 : ℝ), (4818721893/10000000000 : ℝ)] ![(45695118270773/100000000000000 : ℝ), (3171415781937/20000000000000 : ℝ), (38447802807311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749060449/5000000000 : ℝ)|^4335 ≤ (45695118270773/100000000000000 : ℝ)^3311
        have hw : |(2749060449/5000000000 : ℝ)|=(2749060449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2449875071/10000000000 : ℝ)|^4335 ≤ (3171415781937/20000000000000 : ℝ)^3311
        have hw : |(-2449875071/10000000000 : ℝ)|=(2449875071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4818721893/10000000000 : ℝ)|^4335 ≤ (38447802807311/100000000000000 : ℝ)^3311
        have hw : |(4818721893/10000000000 : ℝ)|=(4818721893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5498120783/10000000000 : ℝ)*x 0 + (963744237/2000000000 : ℝ)*x 1 + (-2449876091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5498120783/10000000000 : ℝ)^4335 ≤ (4569511701941/10000000000000 : ℝ)^3311 := by
    have hnat : (5498120783 : ℕ)^4335*10000000000000^3311 ≤ 4569511701941^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498120783 10000000000 4569511701941 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (963744237/2000000000 : ℝ)^4335 ≤ (3844779541121/10000000000000 : ℝ)^3311 := by
    have hnat : (963744237 : ℕ)^4335*10000000000000^3311 ≤ 3844779541121^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963744237 2000000000 3844779541121 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2449876091/10000000000 : ℝ)^4335 ≤ (7928543776789/50000000000000 : ℝ)^3311 := by
    have hnat : (2449876091 : ℕ)^4335*50000000000000^3311 ≤ 7928543776789^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449876091 10000000000 7928543776789 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5498120783/10000000000 : ℝ), (963744237/2000000000 : ℝ), (-2449876091/10000000000 : ℝ)] ![(4569511701941/10000000000000 : ℝ), (3844779541121/10000000000000 : ℝ), (7928543776789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5498120783/10000000000 : ℝ)|^4335 ≤ (4569511701941/10000000000000 : ℝ)^3311
        have hw : |(5498120783/10000000000 : ℝ)|=(5498120783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(963744237/2000000000 : ℝ)|^4335 ≤ (3844779541121/10000000000000 : ℝ)^3311
        have hw : |(963744237/2000000000 : ℝ)|=(963744237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2449876091/10000000000 : ℝ)|^4335 ≤ (7928543776789/50000000000000 : ℝ)^3311
        have hw : |(-2449876091/10000000000 : ℝ)|=(2449876091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173848391/10000000000 : ℝ)*x 0 + (776272801/2500000000 : ℝ)*x 1 + (5573614699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173848391/10000000000 : ℝ)^4335 ≤ (15927559804823/50000000000000 : ℝ)^3311 := by
    have hnat : (4173848391 : ℕ)^4335*50000000000000^3311 ≤ 15927559804823^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173848391 10000000000 15927559804823 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776272801/2500000000 : ℝ)^4335 ≤ (21626543850493/100000000000000 : ℝ)^3311 := by
    have hnat : (776272801 : ℕ)^4335*100000000000000^3311 ≤ 21626543850493^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776272801 2500000000 21626543850493 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5573614699/10000000000 : ℝ)^4335 ≤ (9303667305557/20000000000000 : ℝ)^3311 := by
    have hnat : (5573614699 : ℕ)^4335*20000000000000^3311 ≤ 9303667305557^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573614699 10000000000 9303667305557 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173848391/10000000000 : ℝ), (776272801/2500000000 : ℝ), (5573614699/10000000000 : ℝ)] ![(15927559804823/50000000000000 : ℝ), (21626543850493/100000000000000 : ℝ), (9303667305557/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173848391/10000000000 : ℝ)|^4335 ≤ (15927559804823/50000000000000 : ℝ)^3311
        have hw : |(4173848391/10000000000 : ℝ)|=(4173848391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776272801/2500000000 : ℝ)|^4335 ≤ (21626543850493/100000000000000 : ℝ)^3311
        have hw : |(776272801/2500000000 : ℝ)|=(776272801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5573614699/10000000000 : ℝ)|^4335 ≤ (9303667305557/20000000000000 : ℝ)^3311
        have hw : |(5573614699/10000000000 : ℝ)|=(5573614699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-448520951/2500000000 : ℝ)*x 0 + (2424309759/5000000000 : ℝ)*x 1 + (5951818721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448520951/2500000000 : ℝ)^4335 ≤ (10545740518017/100000000000000 : ℝ)^3311 := by
    have hnat : (448520951 : ℕ)^4335*100000000000000^3311 ≤ 10545740518017^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448520951 2500000000 10545740518017 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2424309759/5000000000 : ℝ)^4335 ≤ (310083413561/800000000000 : ℝ)^3311 := by
    have hnat : (2424309759 : ℕ)^4335*800000000000^3311 ≤ 310083413561^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424309759 5000000000 310083413561 800000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5951818721/10000000000 : ℝ)^4335 ≤ (50693832770743/100000000000000 : ℝ)^3311 := by
    have hnat : (5951818721 : ℕ)^4335*100000000000000^3311 ≤ 50693832770743^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5951818721 10000000000 50693832770743 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448520951/2500000000 : ℝ), (2424309759/5000000000 : ℝ), (5951818721/10000000000 : ℝ)] ![(10545740518017/100000000000000 : ℝ), (310083413561/800000000000 : ℝ), (50693832770743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448520951/2500000000 : ℝ)|^4335 ≤ (10545740518017/100000000000000 : ℝ)^3311
        have hw : |(-448520951/2500000000 : ℝ)|=(448520951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2424309759/5000000000 : ℝ)|^4335 ≤ (310083413561/800000000000 : ℝ)^3311
        have hw : |(2424309759/5000000000 : ℝ)|=(2424309759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5951818721/10000000000 : ℝ)|^4335 ≤ (50693832770743/100000000000000 : ℝ)^3311
        have hw : |(5951818721/10000000000 : ℝ)|=(5951818721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180679173/10000000000 : ℝ)*x 0 + (-263356179/2000000000 : ℝ)*x 1 + (5951817353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180679173/10000000000 : ℝ)^4335 ≤ (4227216256287/10000000000000 : ℝ)^3311 := by
    have hnat : (5180679173 : ℕ)^4335*10000000000000^3311 ≤ 4227216256287^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180679173 10000000000 4227216256287 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263356179/2000000000 : ℝ)^4335 ≤ (7034019900181/100000000000000 : ℝ)^3311 := by
    have hnat : (263356179 : ℕ)^4335*100000000000000^3311 ≤ 7034019900181^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263356179 2000000000 7034019900181 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5951817353/10000000000 : ℝ)^4335 ≤ (50693817515419/100000000000000 : ℝ)^3311 := by
    have hnat : (5951817353 : ℕ)^4335*100000000000000^3311 ≤ 50693817515419^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5951817353 10000000000 50693817515419 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180679173/10000000000 : ℝ), (-263356179/2000000000 : ℝ), (5951817353/10000000000 : ℝ)] ![(4227216256287/10000000000000 : ℝ), (7034019900181/100000000000000 : ℝ), (50693817515419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180679173/10000000000 : ℝ)|^4335 ≤ (4227216256287/10000000000000 : ℝ)^3311
        have hw : |(5180679173/10000000000 : ℝ)|=(5180679173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263356179/2000000000 : ℝ)|^4335 ≤ (7034019900181/100000000000000 : ℝ)^3311
        have hw : |(-263356179/2000000000 : ℝ)|=(263356179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5951817353/10000000000 : ℝ)|^4335 ≤ (50693817515419/100000000000000 : ℝ)^3311
        have hw : |(5951817353/10000000000 : ℝ)|=(5951817353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180677817/10000000000 : ℝ)*x 0 + (2975910083/5000000000 : ℝ)*x 1 + (-658389241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180677817/10000000000 : ℝ)^4335 ≤ (42272148076573/100000000000000 : ℝ)^3311 := by
    have hnat : (5180677817 : ℕ)^4335*100000000000000^3311 ≤ 42272148076573^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180677817 10000000000 42272148076573 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2975910083/5000000000 : ℝ)^4335 ≤ (25346924442369/50000000000000 : ℝ)^3311 := by
    have hnat : (2975910083 : ℕ)^4335*50000000000000^3311 ≤ 25346924442369^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2975910083 5000000000 25346924442369 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658389241/5000000000 : ℝ)^4335 ≤ (3517001511941/50000000000000 : ℝ)^3311 := by
    have hnat : (658389241 : ℕ)^4335*50000000000000^3311 ≤ 3517001511941^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658389241 5000000000 3517001511941 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180677817/10000000000 : ℝ), (2975910083/5000000000 : ℝ), (-658389241/5000000000 : ℝ)] ![(42272148076573/100000000000000 : ℝ), (25346924442369/50000000000000 : ℝ), (3517001511941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180677817/10000000000 : ℝ)|^4335 ≤ (42272148076573/100000000000000 : ℝ)^3311
        have hw : |(5180677817/10000000000 : ℝ)|=(5180677817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2975910083/5000000000 : ℝ)|^4335 ≤ (25346924442369/50000000000000 : ℝ)^3311
        have hw : |(2975910083/5000000000 : ℝ)|=(2975910083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658389241/5000000000 : ℝ)|^4335 ≤ (3517001511941/50000000000000 : ℝ)^3311
        have hw : |(-658389241/5000000000 : ℝ)|=(658389241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s0_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182929761/10000000000 : ℝ)*x 0 + (5510215393/10000000000 : ℝ)*x 1 + (396345219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182929761/10000000000 : ℝ)^4335 ≤ (31945895367637/100000000000000 : ℝ)^3311 := by
    have hnat : (4182929761 : ℕ)^4335*100000000000000^3311 ≤ 31945895367637^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182929761 10000000000 31945895367637 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5510215393/10000000000 : ℝ)^4335 ≤ (45826768254847/100000000000000 : ℝ)^3311 := by
    have hnat : (5510215393 : ℕ)^4335*100000000000000^3311 ≤ 45826768254847^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510215393 10000000000 45826768254847 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396345219/1250000000 : ℝ)^4335 ≤ (2778417044607/12500000000000 : ℝ)^3311 := by
    have hnat : (396345219 : ℕ)^4335*12500000000000^3311 ≤ 2778417044607^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396345219 1250000000 2778417044607 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182929761/10000000000 : ℝ), (5510215393/10000000000 : ℝ), (396345219/1250000000 : ℝ)] ![(31945895367637/100000000000000 : ℝ), (45826768254847/100000000000000 : ℝ), (2778417044607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182929761/10000000000 : ℝ)|^4335 ≤ (31945895367637/100000000000000 : ℝ)^3311
        have hw : |(4182929761/10000000000 : ℝ)|=(4182929761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5510215393/10000000000 : ℝ)|^4335 ≤ (45826768254847/100000000000000 : ℝ)^3311
        have hw : |(5510215393/10000000000 : ℝ)|=(5510215393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396345219/1250000000 : ℝ)|^4335 ≤ (2778417044607/12500000000000 : ℝ)^3311
        have hw : |(396345219/1250000000 : ℝ)|=(396345219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1659/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6659/25000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2167/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2167 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2167*1^512 ≤ 0^512*1^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2167/512 : ℝ) ≤ (1034475016899862567/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2167 ≤ (1034475016899862567/50000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2167*50000000000000000000^512 ≤ 1034475016899862567^512*5^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1034475016899862567 50000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1034475016899862567/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2167 := by
      have hnat : (1 : ℕ)^512*1^2167 ≤ 1^2167*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (51034475016899862567/50000000000000000000 : ℝ) ≤ (5024250892401883/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (51034475016899862567/50000000000000000000 : ℝ)^512 ≤ (5024250892401883/5000000000000000 : ℝ)^2167 := by
      have hnat : (51034475016899862567 : ℕ)^512*5000000000000000^2167 ≤ 5024250892401883^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51034475016899862567 50000000000000000000 5024250892401883 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024250892401883/5000000000000000 : ℝ)) (X := (51034475016899862567/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (26034475016899862567/25000000000000000000 : ℝ) ≤ (2524250892401883/2500000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (26034475016899862567/25000000000000000000 : ℝ)^512 ≤ (2524250892401883/2500000000000000 : ℝ)^2167 := by
      have hnat : (26034475016899862567 : ℕ)^512*2500000000000000^2167 ≤ 2524250892401883^2167*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26034475016899862567 25000000000000000000 2524250892401883 2500000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2524250892401883/2500000000000000 : ℝ)) (X := (26034475016899862567/25000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24250892401883/2000000000000000 : ℝ)*(0 : ℝ))^(2167/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(24250892401883/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1034475016899862567/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24250892401883/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (1 : ℝ)+(24250892401883/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5024250892401883/5000000000000000 : ℝ) by norm_num, show 1+(1034475016899862567/50000000000000000000 : ℝ)+(0 : ℝ)=(51034475016899862567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1034475016899862567/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24250892401883/2000000000000000 : ℝ)*(2/5 : ℝ))^(2167/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(24250892401883/2000000000000000 : ℝ)*(2/5 : ℝ)=(2524250892401883/2500000000000000 : ℝ) by norm_num, show 1+2*(1034475016899862567/50000000000000000000 : ℝ)=(26034475016899862567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24250892401883/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24250892401883/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24250892401883/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24250892401883/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24250892401883/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24250892401883/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1789797307/10000000000 : ℝ)*X 0 0+(299139283/500000000 : ℝ)*X 0 1+(192748851/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2749060449/5000000000 : ℝ)*X 1 0+(-2449875071/10000000000 : ℝ)*X 1 1+(4818721893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5498120783/10000000000 : ℝ)*X 2 0+(963744237/2000000000 : ℝ)*X 2 1+(-2449876091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4173848391/10000000000 : ℝ)*X 0 0+(776272801/2500000000 : ℝ)*X 0 1+(5573614699/10000000000 : ℝ)*X 0 2+(4173848391/10000000000 : ℝ)*X 1 0+(776272801/2500000000 : ℝ)*X 1 1+(5573614699/10000000000 : ℝ)*X 1 2+(4173848391/10000000000 : ℝ)*X 2 0+(776272801/2500000000 : ℝ)*X 2 1+(5573614699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-448520951/2500000000 : ℝ)*X 0 0+(2424309759/5000000000 : ℝ)*X 0 1+(5951818721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180679173/10000000000 : ℝ)*X 1 0+(-263356179/2000000000 : ℝ)*X 1 1+(5951817353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5180677817/10000000000 : ℝ)*X 2 0+(2975910083/5000000000 : ℝ)*X 2 1+(-658389241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4182929761/10000000000 : ℝ)*X 0 0+(5510215393/10000000000 : ℝ)*X 0 1+(396345219/1250000000 : ℝ)*X 0 2+(4182929761/10000000000 : ℝ)*X 1 0+(5510215393/10000000000 : ℝ)*X 1 1+(396345219/1250000000 : ℝ)*X 1 2+(4182929761/10000000000 : ℝ)*X 2 0+(5510215393/10000000000 : ℝ)*X 2 1+(396345219/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13205851990557569876619/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108710227/50000000000000 : ℝ)*(base1) + (13628533/100000000000000 : ℝ)*(base16) + (303146177/25000000000000 : ℝ)*(base19) + (241648967/20000000000000 : ℝ)*(base23) + (224835543/100000000000000 : ℝ)*(upper3) + (15802127011031/2500000000000 : ℝ)*(major0) + (15802127011031/2500000000000 : ℝ)*(major1) + (15802127011031/2500000000000 : ℝ)*(major2) + (859063344821191/100000000000000 : ℝ)*(sp0) + (859064947638091/100000000000000 : ℝ)*(sp1) + (859064965606497/100000000000000 : ℝ)*(sp2) + (25318854964939/6250000000000 : ℝ)*(sp3) + (761612649/25000000000000 : ℝ)*(sp4) + (1914093639/100000000000000 : ℝ)*(sp7) + (405103810953117/100000000000000 : ℝ)*(f.failure) + (214766543462833/25000000000000 : ℝ)*(f.sum) + (3202825933627/2500000000000000000000000000 : ℝ)*base66 + (4273307116373/5000000000000000000000000000 : ℝ)*base67 + (20927051553627/5000000000000000000000000000 : ℝ)*base70 + (2365094266373/5000000000000000000000000000 : ℝ)*base71 + (10368275233627/2500000000000000000000000000 : ℝ)*base74 + (10445548336373/5000000000000000000000000000 : ℝ)*base75 + (14927087101373/5000000000000000000000000000 : ℝ)*base77 + (22771881331373/5000000000000000000000000000 : ℝ)*base79 + (13735139021127/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4263917/2500000000000000000000 : ℝ)*base90 + (4263917/2500000000000000000000 : ℝ)*base92 + (4263917/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (270449781558576462543951/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (574849033/50000000000000 : ℝ)*(base19) + (879756659/50000000000000 : ℝ)*(base23) + (172760793/25000000000000 : ℝ)*(base39) + (33927/50000000000 : ℝ)*(upper2) + (403562659/100000000000000 : ℝ)*(upper5) + (333475210085399/50000000000000 : ℝ)*(major0) + (333475210085399/50000000000000 : ℝ)*(major1) + (333474864563813/50000000000000 : ℝ)*(major2) + (1506564647/50000000000000 : ℝ)*(sp1) + (3685937763/100000000000000 : ℝ)*(sp2) + (90645075487661/10000000000000 : ℝ)*(sp4) + (3625786368197/400000000000 : ℝ)*(sp5) + (9064460004687/1000000000000 : ℝ)*(sp6) + (427449033822101/100000000000000 : ℝ)*(sp7) + (427449033822101/100000000000000 : ℝ)*(f.failure) + (453225722959891/50000000000000 : ℝ)*(f.sum) + (77088747208451/25000000000000000000000000000 : ℝ)*base66 + (187019227559879/100000000000000000000000000000 : ℝ)*base67 + (226829017793683/100000000000000000000000000000 : ℝ)*base70 + (308343717440121/100000000000000000000000000000 : ℝ)*base72 + (114129536591549/25000000000000000000000000000 : ℝ)*base73 + (624334315993683/100000000000000000000000000000 : ℝ)*base76 + (374229760593683/100000000000000000000000000000 : ℝ)*base78 + (557259253606317/100000000000000000000000000000 : ℝ)*base79 + (43261497543683/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3145499/2500000000000000000000 : ℝ)*base89 + (3145499/2500000000000000000000 : ℝ)*base91 + (3145499/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1375_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1659/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6659/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1375_s1_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393971701/2000000000 : ℝ)*x 0 + (1406912577/2500000000 : ℝ)*x 1 + (5058506119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393971701/2000000000 : ℝ)^4335 ≤ (95348407331/800000000000 : ℝ)^3311 := by
    have hnat : (393971701 : ℕ)^4335*800000000000^3311 ≤ 95348407331^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393971701 2000000000 95348407331 800000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406912577/2500000000 : ℝ)^4335 ≤ (11777422229929/25000000000000 : ℝ)^3311 := by
    have hnat : (1406912577 : ℕ)^4335*25000000000000^3311 ≤ 11777422229929^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406912577 2500000000 11777422229929 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5058506119/10000000000 : ℝ)^4335 ≤ (40971760150103/100000000000000 : ℝ)^3311 := by
    have hnat : (5058506119 : ℕ)^4335*100000000000000^3311 ≤ 40971760150103^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058506119 10000000000 40971760150103 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393971701/2000000000 : ℝ), (1406912577/2500000000 : ℝ), (5058506119/10000000000 : ℝ)] ![(95348407331/800000000000 : ℝ), (11777422229929/25000000000000 : ℝ), (40971760150103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393971701/2000000000 : ℝ)|^4335 ≤ (95348407331/800000000000 : ℝ)^3311
        have hw : |(-393971701/2000000000 : ℝ)|=(393971701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1406912577/2500000000 : ℝ)|^4335 ≤ (11777422229929/25000000000000 : ℝ)^3311
        have hw : |(1406912577/2500000000 : ℝ)|=(1406912577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5058506119/10000000000 : ℝ)|^4335 ≤ (40971760150103/100000000000000 : ℝ)^3311
        have hw : |(5058506119/10000000000 : ℝ)|=(5058506119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350575131/2500000000 : ℝ)*x 0 + (-2272729203/10000000000 : ℝ)*x 1 + (2529253741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350575131/2500000000 : ℝ)^4335 ≤ (44655278156687/100000000000000 : ℝ)^3311 := by
    have hnat : (1350575131 : ℕ)^4335*100000000000000^3311 ≤ 44655278156687^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350575131 2500000000 44655278156687 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272729203/10000000000 : ℝ)^4335 ≤ (14372947227227/100000000000000 : ℝ)^3311 := by
    have hnat : (2272729203 : ℕ)^4335*100000000000000^3311 ≤ 14372947227227^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272729203 10000000000 14372947227227 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2529253741/5000000000 : ℝ)^4335 ≤ (20485887302053/50000000000000 : ℝ)^3311 := by
    have hnat : (2529253741 : ℕ)^4335*50000000000000^3311 ≤ 20485887302053^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529253741 5000000000 20485887302053 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350575131/2500000000 : ℝ), (-2272729203/10000000000 : ℝ), (2529253741/5000000000 : ℝ)] ![(44655278156687/100000000000000 : ℝ), (14372947227227/100000000000000 : ℝ), (20485887302053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350575131/2500000000 : ℝ)|^4335 ≤ (44655278156687/100000000000000 : ℝ)^3311
        have hw : |(1350575131/2500000000 : ℝ)|=(1350575131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2272729203/10000000000 : ℝ)|^4335 ≤ (14372947227227/100000000000000 : ℝ)^3311
        have hw : |(-2272729203/10000000000 : ℝ)|=(2272729203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2529253741/5000000000 : ℝ)|^4335 ≤ (20485887302053/50000000000000 : ℝ)^3311
        have hw : |(2529253741/5000000000 : ℝ)|=(2529253741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350575269/2500000000 : ℝ)*x 0 + (632313289/1250000000 : ℝ)*x 1 + (-113636499/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350575269/2500000000 : ℝ)^4335 ≤ (44655284130657/100000000000000 : ℝ)^3311 := by
    have hnat : (1350575269 : ℕ)^4335*100000000000000^3311 ≤ 44655284130657^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350575269 2500000000 44655284130657 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (632313289/1250000000 : ℝ)^4335 ≤ (40971762196781/100000000000000 : ℝ)^3311 := by
    have hnat : (632313289 : ℕ)^4335*100000000000000^3311 ≤ 40971762196781^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632313289 1250000000 40971762196781 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113636499/500000000 : ℝ)^4335 ≤ (7186476830377/50000000000000 : ℝ)^3311 := by
    have hnat : (113636499 : ℕ)^4335*50000000000000^3311 ≤ 7186476830377^3311*500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113636499 500000000 7186476830377 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350575269/2500000000 : ℝ), (632313289/1250000000 : ℝ), (-113636499/500000000 : ℝ)] ![(44655284130657/100000000000000 : ℝ), (40971762196781/100000000000000 : ℝ), (7186476830377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350575269/2500000000 : ℝ)|^4335 ≤ (44655284130657/100000000000000 : ℝ)^3311
        have hw : |(1350575269/2500000000 : ℝ)|=(1350575269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(632313289/1250000000 : ℝ)|^4335 ≤ (40971762196781/100000000000000 : ℝ)^3311
        have hw : |(632313289/1250000000 : ℝ)|=(632313289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113636499/500000000 : ℝ)|^4335 ≤ (7186476830377/50000000000000 : ℝ)^3311
        have hw : |(-113636499/500000000 : ℝ)|=(113636499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071599907/2500000000 : ℝ)*x 0 + (744348919/2000000000 : ℝ)*x 1 + (123216781/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071599907/2500000000 : ℝ)^4335 ≤ (8246111116143/25000000000000 : ℝ)^3311 := by
    have hnat : (1071599907 : ℕ)^4335*25000000000000^3311 ≤ 8246111116143^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071599907 2500000000 8246111116143 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744348919/2000000000 : ℝ)^4335 ≤ (27415138577739/100000000000000 : ℝ)^3311 := by
    have hnat : (744348919 : ℕ)^4335*100000000000000^3311 ≤ 27415138577739^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744348919 2000000000 27415138577739 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (123216781/250000000 : ℝ)^4335 ≤ (19800208468821/50000000000000 : ℝ)^3311 := by
    have hnat : (123216781 : ℕ)^4335*50000000000000^3311 ≤ 19800208468821^3311*250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123216781 250000000 19800208468821 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071599907/2500000000 : ℝ), (744348919/2000000000 : ℝ), (123216781/250000000 : ℝ)] ![(8246111116143/25000000000000 : ℝ), (27415138577739/100000000000000 : ℝ), (19800208468821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071599907/2500000000 : ℝ)|^4335 ≤ (8246111116143/25000000000000 : ℝ)^3311
        have hw : |(1071599907/2500000000 : ℝ)|=(1071599907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744348919/2000000000 : ℝ)|^4335 ≤ (27415138577739/100000000000000 : ℝ)^3311
        have hw : |(744348919/2000000000 : ℝ)|=(744348919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(123216781/250000000 : ℝ)|^4335 ≤ (19800208468821/50000000000000 : ℝ)^3311
        have hw : |(123216781/250000000 : ℝ)|=(123216781/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-197033779/1000000000 : ℝ)*x 0 + (1013093687/2000000000 : ℝ)*x 1 + (2810282293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197033779/1000000000 : ℝ)^4335 ≤ (29805869527/250000000000 : ℝ)^3311 := by
    have hnat : (197033779 : ℕ)^4335*250000000000^3311 ≤ 29805869527^3311*1000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197033779 1000000000 29805869527 250000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013093687/2000000000 : ℝ)^4335 ≤ (20522804045269/50000000000000 : ℝ)^3311 := by
    have hnat : (1013093687 : ℕ)^4335*50000000000000^3311 ≤ 20522804045269^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013093687 2000000000 20522804045269 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2810282293/5000000000 : ℝ)^4335 ≤ (23516022042193/50000000000000 : ℝ)^3311 := by
    have hnat : (2810282293 : ℕ)^4335*50000000000000^3311 ≤ 23516022042193^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810282293 5000000000 23516022042193 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197033779/1000000000 : ℝ), (1013093687/2000000000 : ℝ), (2810282293/5000000000 : ℝ)] ![(29805869527/250000000000 : ℝ), (20522804045269/50000000000000 : ℝ), (23516022042193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197033779/1000000000 : ℝ)|^4335 ≤ (29805869527/250000000000 : ℝ)^3311
        have hw : |(-197033779/1000000000 : ℝ)|=(197033779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013093687/2000000000 : ℝ)|^4335 ≤ (20522804045269/50000000000000 : ℝ)^3311
        have hw : |(1013093687/2000000000 : ℝ)|=(1013093687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2810282293/5000000000 : ℝ)|^4335 ≤ (23516022042193/50000000000000 : ℝ)^3311
        have hw : |(2810282293/5000000000 : ℝ)|=(2810282293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254216219/10000000000 : ℝ)*x 0 + (-171067189/1000000000 : ℝ)*x 1 + (5620564683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254216219/10000000000 : ℝ)^4335 ≤ (1076487141909/2500000000000 : ℝ)^3311 := by
    have hnat : (5254216219 : ℕ)^4335*2500000000000^3311 ≤ 1076487141909^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254216219 10000000000 1076487141909 2500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171067189/1000000000 : ℝ)^4335 ≤ (9908469162561/100000000000000 : ℝ)^3311 := by
    have hnat : (171067189 : ℕ)^4335*100000000000000^3311 ≤ 9908469162561^3311*1000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171067189 1000000000 9908469162561 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620564683/10000000000 : ℝ)^4335 ≤ (23516022573549/50000000000000 : ℝ)^3311 := by
    have hnat : (5620564683 : ℕ)^4335*50000000000000^3311 ≤ 23516022573549^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620564683 10000000000 23516022573549 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254216219/10000000000 : ℝ), (-171067189/1000000000 : ℝ), (5620564683/10000000000 : ℝ)] ![(1076487141909/2500000000000 : ℝ), (9908469162561/100000000000000 : ℝ), (23516022573549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254216219/10000000000 : ℝ)|^4335 ≤ (1076487141909/2500000000000 : ℝ)^3311
        have hw : |(5254216219/10000000000 : ℝ)|=(5254216219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171067189/1000000000 : ℝ)|^4335 ≤ (9908469162561/100000000000000 : ℝ)^3311
        have hw : |(-171067189/1000000000 : ℝ)|=(171067189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620564683/10000000000 : ℝ)|^4335 ≤ (23516022573549/50000000000000 : ℝ)^3311
        have hw : |(5620564683/10000000000 : ℝ)|=(5620564683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050843223/2000000000 : ℝ)*x 0 + (562056479/1000000000 : ℝ)*x 1 + (-855335941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050843223/2000000000 : ℝ)^4335 ≤ (43059484560463/100000000000000 : ℝ)^3311 := by
    have hnat : (1050843223 : ℕ)^4335*100000000000000^3311 ≤ 43059484560463^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050843223 2000000000 43059484560463 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562056479/1000000000 : ℝ)^4335 ≤ (5879005789921/12500000000000 : ℝ)^3311 := by
    have hnat : (562056479 : ℕ)^4335*12500000000000^3311 ≤ 5879005789921^3311*1000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562056479 1000000000 5879005789921 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (855335941/5000000000 : ℝ)^4335 ≤ (9908469101893/100000000000000 : ℝ)^3311 := by
    have hnat : (855335941 : ℕ)^4335*100000000000000^3311 ≤ 9908469101893^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855335941 5000000000 9908469101893 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050843223/2000000000 : ℝ), (562056479/1000000000 : ℝ), (-855335941/5000000000 : ℝ)] ![(43059484560463/100000000000000 : ℝ), (5879005789921/12500000000000 : ℝ), (9908469101893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050843223/2000000000 : ℝ)|^4335 ≤ (43059484560463/100000000000000 : ℝ)^3311
        have hw : |(1050843223/2000000000 : ℝ)|=(1050843223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562056479/1000000000 : ℝ)|^4335 ≤ (5879005789921/12500000000000 : ℝ)^3311
        have hw : |(562056479/1000000000 : ℝ)|=(562056479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-855335941/5000000000 : ℝ)|^4335 ≤ (9908469101893/100000000000000 : ℝ)^3311
        have hw : |(-855335941/5000000000 : ℝ)|=(855335941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s1_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287416743/10000000000 : ℝ)*x 0 + (982781763/2000000000 : ℝ)*x 1 + (467095917/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287416743/10000000000 : ℝ)^4335 ≤ (32994692306791/100000000000000 : ℝ)^3311 := by
    have hnat : (4287416743 : ℕ)^4335*100000000000000^3311 ≤ 32994692306791^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287416743 10000000000 32994692306791 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982781763/2000000000 : ℝ)^4335 ≤ (39445193893357/100000000000000 : ℝ)^3311 := by
    have hnat : (982781763 : ℕ)^4335*100000000000000^3311 ≤ 39445193893357^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982781763 2000000000 39445193893357 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467095917/1250000000 : ℝ)^4335 ≤ (1102404551213/4000000000000 : ℝ)^3311 := by
    have hnat : (467095917 : ℕ)^4335*4000000000000^3311 ≤ 1102404551213^3311*1250000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467095917 1250000000 1102404551213 4000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287416743/10000000000 : ℝ), (982781763/2000000000 : ℝ), (467095917/1250000000 : ℝ)] ![(32994692306791/100000000000000 : ℝ), (39445193893357/100000000000000 : ℝ), (1102404551213/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287416743/10000000000 : ℝ)|^4335 ≤ (32994692306791/100000000000000 : ℝ)^3311
        have hw : |(4287416743/10000000000 : ℝ)|=(4287416743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(982781763/2000000000 : ℝ)|^4335 ≤ (39445193893357/100000000000000 : ℝ)^3311
        have hw : |(982781763/2000000000 : ℝ)|=(982781763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467095917/1250000000 : ℝ)|^4335 ≤ (1102404551213/4000000000000 : ℝ)^3311
        have hw : |(467095917/1250000000 : ℝ)|=(467095917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6659/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1659/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (719/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19219/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6659/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1659/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6659/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1659/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6659/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1659/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6659/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1659/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6659/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1659/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6659/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1659/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1659/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (2921722084971/100000000000000000000 : ℝ) := by
    have hpowers : (1659/100000 : ℝ)^2167 ≤ (2921722084971/100000000000000000000 : ℝ)^512 := by
      have hnat : (1659 : ℕ)^2167*100000000000000000000^512 ≤ 2921722084971^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1659 100000 2921722084971 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1659/100000 : ℝ)) (X := (2921722084971/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (6659/25000 : ℝ) ^ (2167/512 : ℝ) ≤ (370119915259740931/100000000000000000000 : ℝ) := by
    have hpowers : (6659/25000 : ℝ)^2167 ≤ (370119915259740931/100000000000000000000 : ℝ)^512 := by
      have hnat : (6659 : ℕ)^2167*100000000000000000000^512 ≤ 370119915259740931^512*25000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6659 25000 370119915259740931 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6659/25000 : ℝ)) (X := (370119915259740931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000002921722084971/50000000000000000000 : ℝ) ≤ (5000000069031919/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50000002921722084971/50000000000000000000 : ℝ)^512 ≤ (5000000069031919/5000000000000000 : ℝ)^2167 := by
      have hnat : (50000002921722084971 : ℕ)^512*5000000000000000^2167 ≤ 5000000069031919^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000002921722084971 50000000000000000000 5000000069031919 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000069031919/5000000000000000 : ℝ)) (X := (50000002921722084971/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50185061418490912951/50000000000000000000 : ℝ) ≤ (80069860871881/80000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50185061418490912951/50000000000000000000 : ℝ)^512 ≤ (80069860871881/80000000000000 : ℝ)^2167 := by
      have hnat : (50185061418490912951 : ℕ)^512*80000000000000^2167 ≤ 80069860871881^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50185061418490912951 50000000000000000000 80069860871881 80000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80069860871881/80000000000000 : ℝ)) (X := (50185061418490912951/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50370119915259740931/50000000000000000000 : ℝ) ≤ (2504366269976603/2500000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50370119915259740931/50000000000000000000 : ℝ)^512 ≤ (2504366269976603/2500000000000000 : ℝ)^2167 := by
      have hnat : (50370119915259740931 : ℕ)^512*2500000000000000^2167 ≤ 2504366269976603^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50370119915259740931 50000000000000000000 2504366269976603 2500000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504366269976603/2500000000000000 : ℝ)) (X := (50370119915259740931/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2921722084971/100000000000000000000 : ℝ) ≤ ((12487051455495182573/12488500000000000000 : ℝ)+2*(8732470921287/2497700000000000 : ℝ)*(1659/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (12487051455495182573/12488500000000000000 : ℝ)+2*(8732470921287/2497700000000000 : ℝ)*(1659/100000 : ℝ)=(5000000069031919/5000000000000000 : ℝ) by norm_num, show 1+2*(2921722084971/100000000000000000000 : ℝ)=(50000002921722084971/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(370119915259740931/100000000000000000000 : ℝ)+(2921722084971/100000000000000000000 : ℝ) ≤ ((12487051455495182573/12488500000000000000 : ℝ)+(8732470921287/2497700000000000 : ℝ)*((6659/25000 : ℝ)+(1659/100000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (12487051455495182573/12488500000000000000 : ℝ)+(8732470921287/2497700000000000 : ℝ)*((6659/25000 : ℝ)+(1659/100000 : ℝ))=(80069860871881/80000000000000 : ℝ) by norm_num, show 1+(370119915259740931/100000000000000000000 : ℝ)+(2921722084971/100000000000000000000 : ℝ)=(50185061418490912951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(370119915259740931/100000000000000000000 : ℝ) ≤ ((12487051455495182573/12488500000000000000 : ℝ)+2*(8732470921287/2497700000000000 : ℝ)*(6659/25000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (12487051455495182573/12488500000000000000 : ℝ)+2*(8732470921287/2497700000000000 : ℝ)*(6659/25000 : ℝ)=(2504366269976603/2500000000000000 : ℝ) by norm_num, show 1+2*(370119915259740931/100000000000000000000 : ℝ)=(50370119915259740931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12487051455495182573/12488500000000000000 : ℝ)*(X 1 0+X 2 0)+(8732470921287/2497700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (1659/100000 : ℝ)) (hi := (6659/25000 : ℝ)) (c := (12487051455495182573/12488500000000000000 : ℝ)) (alpha := (8732470921287/2497700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12487051455495182573/12488500000000000000 : ℝ)*(X 0 1+X 2 1)+(8732470921287/2497700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (1659/100000 : ℝ)) (hi := (6659/25000 : ℝ)) (c := (12487051455495182573/12488500000000000000 : ℝ)) (alpha := (8732470921287/2497700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12487051455495182573/12488500000000000000 : ℝ)*(X 0 2+X 1 2)+(8732470921287/2497700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (1659/100000 : ℝ)) (hi := (6659/25000 : ℝ)) (c := (12487051455495182573/12488500000000000000 : ℝ)) (alpha := (8732470921287/2497700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393971701/2000000000 : ℝ)*X 0 0+(1406912577/2500000000 : ℝ)*X 0 1+(5058506119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1350575131/2500000000 : ℝ)*X 1 0+(-2272729203/10000000000 : ℝ)*X 1 1+(2529253741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1350575269/2500000000 : ℝ)*X 2 0+(632313289/1250000000 : ℝ)*X 2 1+(-113636499/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071599907/2500000000 : ℝ)*X 0 0+(744348919/2000000000 : ℝ)*X 0 1+(123216781/250000000 : ℝ)*X 0 2+(1071599907/2500000000 : ℝ)*X 1 0+(744348919/2000000000 : ℝ)*X 1 1+(123216781/250000000 : ℝ)*X 1 2+(1071599907/2500000000 : ℝ)*X 2 0+(744348919/2000000000 : ℝ)*X 2 1+(123216781/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-197033779/1000000000 : ℝ)*X 0 0+(1013093687/2000000000 : ℝ)*X 0 1+(2810282293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254216219/10000000000 : ℝ)*X 1 0+(-171067189/1000000000 : ℝ)*X 1 1+(5620564683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1050843223/2000000000 : ℝ)*X 2 0+(562056479/1000000000 : ℝ)*X 2 1+(-855335941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287416743/10000000000 : ℝ)*X 0 0+(982781763/2000000000 : ℝ)*X 0 1+(467095917/1250000000 : ℝ)*X 0 2+(4287416743/10000000000 : ℝ)*X 1 0+(982781763/2000000000 : ℝ)*X 1 1+(467095917/1250000000 : ℝ)*X 1 2+(4287416743/10000000000 : ℝ)*X 2 0+(982781763/2000000000 : ℝ)*X 2 1+(467095917/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101062862032961411262135993/39026562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3195633/1562500000000 : ℝ)*(base19) + (84810691/20000000000000 : ℝ)*(base23) + (11642617/25000000000000 : ℝ)*(upper2) + (6759469/100000000000000 : ℝ)*(lower5) + (80799661565949/6250000000000 : ℝ)*(major0) + (80799661565949/6250000000000 : ℝ)*(major1) + (80799661565949/6250000000000 : ℝ)*(major2) + (878514993813479/50000000000000 : ℝ)*(sp0) + (439258960510803/25000000000000 : ℝ)*(sp1) + (439258484238701/25000000000000 : ℝ)*(sp2) + (207137956659979/25000000000000 : ℝ)*(sp3) + (3029468383/50000000000000 : ℝ)*(sp4) + (842777733/50000000000000 : ℝ)*(sp6) + (1210587/100000000000 : ℝ)*(sp7) + (207138259306729/25000000000000 : ℝ)*(f.failure) + (439259011640931/25000000000000 : ℝ)*(f.sum) + (69828262096689/62442500000000000000000000000 : ℝ)*base65 + (167643014865171973/78053125000000000000000000000000 : ℝ)*base68 + (260388034625321973/78053125000000000000000000000000 : ℝ)*base70 + (468388889655903223/78053125000000000000000000000000 : ℝ)*base72 + (47560412660621/15610625000000000000000000000 : ℝ)*base73 + (334069193818953223/78053125000000000000000000000000 : ℝ)*base76 + (513492715768596973/78053125000000000000000000000000 : ℝ)*base78 + (610405666407603223/78053125000000000000000000000000 : ℝ)*base80 + (10521293436557/31221250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2833671/625000000000000000000 : ℝ)*base89 + (2833671/625000000000000000000 : ℝ)*base91 + (2833671/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (683128348937156375324381307/312212500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9728171/50000000000000 : ℝ)*(base1) + (222042161/50000000000000 : ℝ)*(base19) + (25683677/6250000000000 : ℝ)*(base23) + (29484279/50000000000000 : ℝ)*(upper3) + (9206823/20000000000000 : ℝ)*(upper5) + (1325502568068853/100000000000000 : ℝ)*(major0) + (1325502568068853/100000000000000 : ℝ)*(major1) + (1325502568068853/100000000000000 : ℝ)*(major2) + (157962329/6250000000000 : ℝ)*(sp1) + (2616532759/100000000000000 : ℝ)*(sp2) + (900744737065703/50000000000000 : ℝ)*(sp4) + (900743241596739/50000000000000 : ℝ)*(sp5) + (1801486427203473/100000000000000 : ℝ)*(sp6) + (424757794536087/50000000000000 : ℝ)*(sp7) + (212378902132129/25000000000000 : ℝ)*(f.failure) + (225186181834383/12500000000000 : ℝ)*(f.sum) + (63410459926141/124885000000000000000000000000 : ℝ)*base65 + (7205980309928246231/1248850000000000000000000000000000 : ℝ)*base68 + (678881970024246231/1248850000000000000000000000000000 : ℝ)*base70 + (702983426266246231/1248850000000000000000000000000000 : ℝ)*base72 + (410328705699419/124885000000000000000000000000 : ℝ)*base74 + (2875707536897346231/1248850000000000000000000000000000 : ℝ)*base76 + (5704203957053903769/1248850000000000000000000000000000 : ℝ)*base77 + (6370026180930046231/1248850000000000000000000000000000 : ℝ)*base80 + (209971661418519/124885000000000000000000000000 : ℝ)*base82 + (1798271/625000000000000000000 : ℝ)*base89 + (1798271/625000000000000000000 : ℝ)*base91 + (1798271/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1375_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6659/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1659/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (719/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19219/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1375_s2_0 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-80288991/400000000 : ℝ)*x 0 + (2735523277/5000000000 : ℝ)*x 1 + (1297782497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80288991/400000000 : ℝ)^4335 ≤ (3053854942897/25000000000000 : ℝ)^3311 := by
    have hnat : (80288991 : ℕ)^4335*25000000000000^3311 ≤ 3053854942897^3311*400000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80288991 400000000 3053854942897 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735523277/5000000000 : ℝ)^4335 ≤ (9080147128461/20000000000000 : ℝ)^3311 := by
    have hnat : (2735523277 : ℕ)^4335*20000000000000^3311 ≤ 9080147128461^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735523277 5000000000 9080147128461 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297782497/2500000000 : ℝ)^4335 ≤ (1324495143047/3125000000000 : ℝ)^3311 := by
    have hnat : (1297782497 : ℕ)^4335*3125000000000^3311 ≤ 1324495143047^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297782497 2500000000 1324495143047 3125000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80288991/400000000 : ℝ), (2735523277/5000000000 : ℝ), (1297782497/2500000000 : ℝ)] ![(3053854942897/25000000000000 : ℝ), (9080147128461/20000000000000 : ℝ), (1324495143047/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80288991/400000000 : ℝ)|^4335 ≤ (3053854942897/25000000000000 : ℝ)^3311
        have hw : |(-80288991/400000000 : ℝ)|=(80288991/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735523277/5000000000 : ℝ)|^4335 ≤ (9080147128461/20000000000000 : ℝ)^3311
        have hw : |(2735523277/5000000000 : ℝ)|=(2735523277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297782497/2500000000 : ℝ)|^4335 ≤ (1324495143047/3125000000000 : ℝ)^3311
        have hw : |(1297782497/2500000000 : ℝ)|=(1297782497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_1 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167614831/312500000 : ℝ)*x 0 + (-2151608153/10000000000 : ℝ)*x 1 + (2595565053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167614831/312500000 : ℝ)^4335 ≤ (22118857716371/50000000000000 : ℝ)^3311 := by
    have hnat : (167614831 : ℕ)^4335*50000000000000^3311 ≤ 22118857716371^3311*312500000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167614831 312500000 22118857716371 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151608153/10000000000 : ℝ)^4335 ≤ (6689219359173/50000000000000 : ℝ)^3311 := by
    have hnat : (2151608153 : ℕ)^4335*50000000000000^3311 ≤ 6689219359173^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151608153 10000000000 6689219359173 50000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595565053/5000000000 : ℝ)^4335 ≤ (42383845838897/100000000000000 : ℝ)^3311 := by
    have hnat : (2595565053 : ℕ)^4335*100000000000000^3311 ≤ 42383845838897^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595565053 5000000000 42383845838897 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167614831/312500000 : ℝ), (-2151608153/10000000000 : ℝ), (2595565053/5000000000 : ℝ)] ![(22118857716371/50000000000000 : ℝ), (6689219359173/50000000000000 : ℝ), (42383845838897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167614831/312500000 : ℝ)|^4335 ≤ (22118857716371/50000000000000 : ℝ)^3311
        have hw : |(167614831/312500000 : ℝ)|=(167614831/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2151608153/10000000000 : ℝ)|^4335 ≤ (6689219359173/50000000000000 : ℝ)^3311
        have hw : |(-2151608153/10000000000 : ℝ)|=(2151608153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595565053/5000000000 : ℝ)|^4335 ≤ (42383845838897/100000000000000 : ℝ)^3311
        have hw : |(2595565053/5000000000 : ℝ)|=(2595565053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_2 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335229659/625000000 : ℝ)*x 0 + (259556507/500000000 : ℝ)*x 1 + (-215160817/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335229659/625000000 : ℝ)^4335 ≤ (44237714914417/100000000000000 : ℝ)^3311 := by
    have hnat : (335229659 : ℕ)^4335*100000000000000^3311 ≤ 44237714914417^3311*625000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335229659 625000000 44237714914417 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259556507/500000000 : ℝ)^4335 ≤ (847676924047/2000000000000 : ℝ)^3311 := by
    have hnat : (259556507 : ℕ)^4335*2000000000000^3311 ≤ 847676924047^3311*500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259556507 500000000 847676924047 2000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215160817/1000000000 : ℝ)^4335 ≤ (13378438856741/100000000000000 : ℝ)^3311 := by
    have hnat : (215160817 : ℕ)^4335*100000000000000^3311 ≤ 13378438856741^3311*1000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215160817 1000000000 13378438856741 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335229659/625000000 : ℝ), (259556507/500000000 : ℝ), (-215160817/1000000000 : ℝ)] ![(44237714914417/100000000000000 : ℝ), (847676924047/2000000000000 : ℝ), (13378438856741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335229659/625000000 : ℝ)|^4335 ≤ (44237714914417/100000000000000 : ℝ)^3311
        have hw : |(335229659/625000000 : ℝ)|=(335229659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259556507/500000000 : ℝ)|^4335 ≤ (847676924047/2000000000000 : ℝ)^3311
        have hw : |(259556507/500000000 : ℝ)|=(259556507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215160817/1000000000 : ℝ)|^4335 ≤ (13378438856741/100000000000000 : ℝ)^3311
        have hw : |(-215160817/1000000000 : ℝ)|=(215160817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_3 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172505059/400000000 : ℝ)*x 0 + (4025214073/10000000000 : ℝ)*x 1 + (2309403493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172505059/400000000 : ℝ)^4335 ≤ (33248930447031/100000000000000 : ℝ)^3311 := by
    have hnat : (172505059 : ℕ)^4335*100000000000000^3311 ≤ 33248930447031^3311*400000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172505059 400000000 33248930447031 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025214073/10000000000 : ℝ)^4335 ≤ (30378143680513/100000000000000 : ℝ)^3311 := by
    have hnat : (4025214073 : ℕ)^4335*100000000000000^3311 ≤ 30378143680513^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025214073 10000000000 30378143680513 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2309403493/5000000000 : ℝ)^4335 ≤ (4546615731997/12500000000000 : ℝ)^3311 := by
    have hnat : (2309403493 : ℕ)^4335*12500000000000^3311 ≤ 4546615731997^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309403493 5000000000 4546615731997 12500000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172505059/400000000 : ℝ), (4025214073/10000000000 : ℝ), (2309403493/5000000000 : ℝ)] ![(33248930447031/100000000000000 : ℝ), (30378143680513/100000000000000 : ℝ), (4546615731997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172505059/400000000 : ℝ)|^4335 ≤ (33248930447031/100000000000000 : ℝ)^3311
        have hw : |(172505059/400000000 : ℝ)|=(172505059/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025214073/10000000000 : ℝ)|^4335 ≤ (30378143680513/100000000000000 : ℝ)^3311
        have hw : |(4025214073/10000000000 : ℝ)|=(4025214073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2309403493/5000000000 : ℝ)|^4335 ≤ (4546615731997/12500000000000 : ℝ)^3311
        have hw : |(2309403493/5000000000 : ℝ)|=(2309403493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_4 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-501820413/2500000000 : ℝ)*x 0 + (2596411987/5000000000 : ℝ)*x 1 + (5469337981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501820413/2500000000 : ℝ)^4335 ≤ (12215872962187/100000000000000 : ℝ)^3311 := by
    have hnat : (501820413 : ℕ)^4335*100000000000000^3311 ≤ 12215872962187^3311*2500000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501820413 2500000000 12215872962187 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596411987/5000000000 : ℝ)^4335 ≤ (8480390762423/20000000000000 : ℝ)^3311 := by
    have hnat : (2596411987 : ℕ)^4335*20000000000000^3311 ≤ 8480390762423^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596411987 5000000000 8480390762423 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469337981/10000000000 : ℝ)^4335 ≤ (45382173206493/100000000000000 : ℝ)^3311 := by
    have hnat : (5469337981 : ℕ)^4335*100000000000000^3311 ≤ 45382173206493^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469337981 10000000000 45382173206493 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501820413/2500000000 : ℝ), (2596411987/5000000000 : ℝ), (5469337981/10000000000 : ℝ)] ![(12215872962187/100000000000000 : ℝ), (8480390762423/20000000000000 : ℝ), (45382173206493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501820413/2500000000 : ℝ)|^4335 ≤ (12215872962187/100000000000000 : ℝ)^3311
        have hw : |(-501820413/2500000000 : ℝ)|=(501820413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596411987/5000000000 : ℝ)|^4335 ≤ (8480390762423/20000000000000 : ℝ)^3311
        have hw : |(2596411987/5000000000 : ℝ)|=(2596411987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469337981/10000000000 : ℝ)|^4335 ≤ (45382173206493/100000000000000 : ℝ)^3311
        have hw : |(5469337981/10000000000 : ℝ)|=(5469337981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_5 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291273511/10000000000 : ℝ)*x 0 + (-936700417/5000000000 : ℝ)*x 1 + (5469337689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291273511/10000000000 : ℝ)^4335 ≤ (43457535217423/100000000000000 : ℝ)^3311 := by
    have hnat : (5291273511 : ℕ)^4335*100000000000000^3311 ≤ 43457535217423^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291273511 10000000000 43457535217423 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936700417/5000000000 : ℝ)^4335 ≤ (1116029473923/10000000000000 : ℝ)^3311 := by
    have hnat : (936700417 : ℕ)^4335*10000000000000^3311 ≤ 1116029473923^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936700417 5000000000 1116029473923 10000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469337689/10000000000 : ℝ)^4335 ≤ (45382170034273/100000000000000 : ℝ)^3311 := by
    have hnat : (5469337689 : ℕ)^4335*100000000000000^3311 ≤ 45382170034273^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469337689 10000000000 45382170034273 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291273511/10000000000 : ℝ), (-936700417/5000000000 : ℝ), (5469337689/10000000000 : ℝ)] ![(43457535217423/100000000000000 : ℝ), (1116029473923/10000000000000 : ℝ), (45382170034273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291273511/10000000000 : ℝ)|^4335 ≤ (43457535217423/100000000000000 : ℝ)^3311
        have hw : |(5291273511/10000000000 : ℝ)|=(5291273511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-936700417/5000000000 : ℝ)|^4335 ≤ (1116029473923/10000000000000 : ℝ)^3311
        have hw : |(-936700417/5000000000 : ℝ)|=(936700417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469337689/10000000000 : ℝ)|^4335 ≤ (45382170034273/100000000000000 : ℝ)^3311
        have hw : |(5469337689/10000000000 : ℝ)|=(5469337689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_6 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058254999/2000000000 : ℝ)*x 0 + (2734668907/5000000000 : ℝ)*x 1 + (-1873398613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058254999/2000000000 : ℝ)^4335 ≤ (8691510235013/20000000000000 : ℝ)^3311 := by
    have hnat : (1058254999 : ℕ)^4335*20000000000000^3311 ≤ 8691510235013^3311*2000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058254999 2000000000 8691510235013 20000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734668907/5000000000 : ℝ)^4335 ≤ (11345542848061/25000000000000 : ℝ)^3311 := by
    have hnat : (2734668907 : ℕ)^4335*25000000000000^3311 ≤ 11345542848061^3311*5000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734668907 5000000000 11345542848061 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873398613/10000000000 : ℝ)^4335 ≤ (558013870811/5000000000000 : ℝ)^3311 := by
    have hnat : (1873398613 : ℕ)^4335*5000000000000^3311 ≤ 558013870811^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873398613 10000000000 558013870811 5000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058254999/2000000000 : ℝ), (2734668907/5000000000 : ℝ), (-1873398613/10000000000 : ℝ)] ![(8691510235013/20000000000000 : ℝ), (11345542848061/25000000000000 : ℝ), (558013870811/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058254999/2000000000 : ℝ)|^4335 ≤ (8691510235013/20000000000000 : ℝ)^3311
        have hw : |(1058254999/2000000000 : ℝ)|=(1058254999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734668907/5000000000 : ℝ)|^4335 ≤ (11345542848061/25000000000000 : ℝ)^3311
        have hw : |(2734668907/5000000000 : ℝ)|=(2734668907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1873398613/10000000000 : ℝ)|^4335 ≤ (558013870811/5000000000000 : ℝ)^3311
        have hw : |(-1873398613/10000000000 : ℝ)|=(1873398613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1375_s2_7 (p : ℝ) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312748833/10000000000 : ℝ)*x 0 + (4615215471/10000000000 : ℝ)*x 1 + (4028835727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312748833/10000000000 : ℝ)^4335 ≤ (8312541385271/25000000000000 : ℝ)^3311 := by
    have hnat : (4312748833 : ℕ)^4335*25000000000000^3311 ≤ 8312541385271^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312748833 10000000000 8312541385271 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4615215471/10000000000 : ℝ)^4335 ≤ (36335900111831/100000000000000 : ℝ)^3311 := by
    have hnat : (4615215471 : ℕ)^4335*100000000000000^3311 ≤ 36335900111831^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615215471 10000000000 36335900111831 100000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028835727/10000000000 : ℝ)^4335 ≤ (7603483581589/25000000000000 : ℝ)^3311 := by
    have hnat : (4028835727 : ℕ)^4335*25000000000000^3311 ≤ 7603483581589^3311*10000000000^4335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028835727 10000000000 7603483581589 25000000000000 4335 3311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4335/1024 : ℝ)) 4335 3311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312748833/10000000000 : ℝ), (4615215471/10000000000 : ℝ), (4028835727/10000000000 : ℝ)] ![(8312541385271/25000000000000 : ℝ), (36335900111831/100000000000000 : ℝ), (7603483581589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312748833/10000000000 : ℝ)|^4335 ≤ (8312541385271/25000000000000 : ℝ)^3311
        have hw : |(4312748833/10000000000 : ℝ)|=(4312748833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4615215471/10000000000 : ℝ)|^4335 ≤ (36335900111831/100000000000000 : ℝ)^3311
        have hw : |(4615215471/10000000000 : ℝ)|=(4615215471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028835727/10000000000 : ℝ)|^4335 ≤ (7603483581589/25000000000000 : ℝ)^3311
        have hw : |(4028835727/10000000000 : ℝ)|=(4028835727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1375_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (719/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (503/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15979/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (719/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (719/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (719/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (719/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (719/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (719/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (719/10000 : ℝ) ^ (2167/512 : ℝ) ≤ (724710161717033/50000000000000000000 : ℝ) := by
    have hpowers : (719/10000 : ℝ)^2167 ≤ (724710161717033/50000000000000000000 : ℝ)^512 := by
      have hnat : (719 : ℕ)^2167*50000000000000000000^512 ≤ 724710161717033^512*10000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        719 10000 724710161717033 50000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (719/10000 : ℝ)) (X := (724710161717033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hpowhi : (19219/100000 : ℝ) ^ (2167/512 : ℝ) ≤ (92992198124669783/100000000000000000000 : ℝ) := by
    have hpowers : (19219/100000 : ℝ)^2167 ≤ (92992198124669783/100000000000000000000 : ℝ)^512 := by
      have hnat : (19219 : ℕ)^2167*100000000000000000000^512 ≤ 92992198124669783^512*100000^2167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19219 100000 92992198124669783 100000000000000000000 2167 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19219/100000 : ℝ)) (X := (92992198124669783/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000724710161717033/25000000000000000000 : ℝ) ≤ (250001712263477/250000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (25000724710161717033/25000000000000000000 : ℝ)^512 ≤ (250001712263477/250000000000000 : ℝ)^2167 := by
      have hnat : (25000724710161717033 : ℕ)^512*250000000000000^2167 ≤ 250001712263477^2167*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000724710161717033 25000000000000000000 250001712263477 250000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250001712263477/250000000000000 : ℝ)) (X := (25000724710161717033/25000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100094441618448103849/100000000000000000000 : ℝ) ≤ (5001115290261911/5000000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (100094441618448103849/100000000000000000000 : ℝ)^512 ≤ (5001115290261911/5000000000000000 : ℝ)^2167 := by
      have hnat : (100094441618448103849 : ℕ)^512*5000000000000000^2167 ≤ 5001115290261911^2167*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100094441618448103849 100000000000000000000 5001115290261911 5000000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001115290261911/5000000000000000 : ℝ)) (X := (100094441618448103849/100000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50092992198124669783/50000000000000000000 : ℝ) ≤ (2501098167627141/2500000000000000 : ℝ) ^ (2167/512 : ℝ) := by
    have hpowers : (50092992198124669783/50000000000000000000 : ℝ)^512 ≤ (2501098167627141/2500000000000000 : ℝ)^2167 := by
      have hnat : (50092992198124669783 : ℕ)^512*2500000000000000^2167 ≤ 2501098167627141^2167*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50092992198124669783 50000000000000000000 2501098167627141 2500000000000000 512 2167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501098167627141/2500000000000000 : ℝ)) (X := (50092992198124669783/50000000000000000000 : ℝ)) (by norm_num) 2167 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(724710161717033/50000000000000000000 : ℝ) ≤ ((751623331366962521/751812500000000000 : ℝ)+2*(1081044992371/601450000000000 : ℝ)*(719/10000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (751623331366962521/751812500000000000 : ℝ)+2*(1081044992371/601450000000000 : ℝ)*(719/10000 : ℝ)=(250001712263477/250000000000000 : ℝ) by norm_num, show 1+2*(724710161717033/50000000000000000000 : ℝ)=(25000724710161717033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(92992198124669783/100000000000000000000 : ℝ)+(724710161717033/50000000000000000000 : ℝ) ≤ ((751623331366962521/751812500000000000 : ℝ)+(1081044992371/601450000000000 : ℝ)*((19219/100000 : ℝ)+(719/10000 : ℝ)))^(2167/512 : ℝ) := by
    rw [show (751623331366962521/751812500000000000 : ℝ)+(1081044992371/601450000000000 : ℝ)*((19219/100000 : ℝ)+(719/10000 : ℝ))=(5001115290261911/5000000000000000 : ℝ) by norm_num, show 1+(92992198124669783/100000000000000000000 : ℝ)+(724710161717033/50000000000000000000 : ℝ)=(100094441618448103849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(92992198124669783/100000000000000000000 : ℝ) ≤ ((751623331366962521/751812500000000000 : ℝ)+2*(1081044992371/601450000000000 : ℝ)*(19219/100000 : ℝ))^(2167/512 : ℝ) := by
    rw [show (751623331366962521/751812500000000000 : ℝ)+2*(1081044992371/601450000000000 : ℝ)*(19219/100000 : ℝ)=(2501098167627141/2500000000000000 : ℝ) by norm_num, show 1+2*(92992198124669783/100000000000000000000 : ℝ)=(50092992198124669783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (751623331366962521/751812500000000000 : ℝ)*(X 1 0+X 2 0)+(1081044992371/601450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (719/10000 : ℝ)) (hi := (19219/100000 : ℝ)) (c := (751623331366962521/751812500000000000 : ℝ)) (alpha := (1081044992371/601450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (751623331366962521/751812500000000000 : ℝ)*(X 0 1+X 2 1)+(1081044992371/601450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (719/10000 : ℝ)) (hi := (19219/100000 : ℝ)) (c := (751623331366962521/751812500000000000 : ℝ)) (alpha := (1081044992371/601450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (751623331366962521/751812500000000000 : ℝ)*(X 0 2+X 1 2)+(1081044992371/601450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2167/512 : ℝ)) (lo := (719/10000 : ℝ)) (hi := (19219/100000 : ℝ)) (c := (751623331366962521/751812500000000000 : ℝ)) (alpha := (1081044992371/601450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-80288991/400000000 : ℝ)*X 0 0+(2735523277/5000000000 : ℝ)*X 0 1+(1297782497/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167614831/312500000 : ℝ)*X 1 0+(-2151608153/10000000000 : ℝ)*X 1 1+(2595565053/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335229659/625000000 : ℝ)*X 2 0+(259556507/500000000 : ℝ)*X 2 1+(-215160817/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172505059/400000000 : ℝ)*X 0 0+(4025214073/10000000000 : ℝ)*X 0 1+(2309403493/5000000000 : ℝ)*X 0 2+(172505059/400000000 : ℝ)*X 1 0+(4025214073/10000000000 : ℝ)*X 1 1+(2309403493/5000000000 : ℝ)*X 1 2+(172505059/400000000 : ℝ)*X 2 0+(4025214073/10000000000 : ℝ)*X 2 1+(2309403493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-501820413/2500000000 : ℝ)*X 0 0+(2596411987/5000000000 : ℝ)*X 0 1+(5469337981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291273511/10000000000 : ℝ)*X 1 0+(-936700417/5000000000 : ℝ)*X 1 1+(5469337689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058254999/2000000000 : ℝ)*X 2 0+(2734668907/5000000000 : ℝ)*X 2 1+(-1873398613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312748833/10000000000 : ℝ)*X 0 0+(4615215471/10000000000 : ℝ)*X 0 1+(4028835727/10000000000 : ℝ)*X 0 2+(4312748833/10000000000 : ℝ)*X 1 0+(4615215471/10000000000 : ℝ)*X 1 1+(4028835727/10000000000 : ℝ)*X 1 2+(4312748833/10000000000 : ℝ)*X 2 0+(4615215471/10000000000 : ℝ)*X 2 1+(4028835727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1375_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (977469093642346426212477/163437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (494745481/50000000000000 : ℝ)*(base19) + (890014547/100000000000000 : ℝ)*(base23) + (18103909/50000000000000 : ℝ)*(lower2) + (39025473/25000000000000 : ℝ)*(upper3) + (8112917/10000000000000 : ℝ)*(upper5) + (4107178654747/156250000000 : ℝ)*(major0) + (4107178654747/156250000000 : ℝ)*(major1) + (4107178654747/156250000000 : ℝ)*(major2) + (446563418856619/12500000000000 : ℝ)*(sp0) + (1786259684577143/50000000000000 : ℝ)*(sp1) + (35725194686307/1000000000000 : ℝ)*(sp2) + (1684661737050873/100000000000000 : ℝ)*(sp3) + (1625974037/12500000000000 : ℝ)*(sp4) + (19946949/312500000000 : ℝ)*(sp7) + (210583515009319/12500000000000 : ℝ)*(f.failure) + (6977578825479/195312500000 : ℝ)*(f.sum) + (403143314533/104600000000000000000000000 : ℝ)*base66 + (745798321931659/326875000000000000000000000000 : ℝ)*base68 + (1038843620024267/163437500000000000000000000000 : ℝ)*base70 + (1542846832294591/326875000000000000000000000000 : ℝ)*base71 + (3014858873009/523000000000000000000000000 : ℝ)*base74 + (295457618921983/163437500000000000000000000000 : ℝ)*base75 + (1614497999654591/326875000000000000000000000000 : ℝ)*base77 + (3890052010178341/326875000000000000000000000000 : ℝ)*base79 + (403397661391/52300000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3184919/312500000000000000000 : ℝ)*base90 + (3184919/312500000000000000000 : ℝ)*base92 + (3184919/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22204905601791952439727741/7518125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777789137/100000000000000 : ℝ)*(base19) + (1355963247/50000000000000 : ℝ)*(base23) + (1223419/2000000000000 : ℝ)*(lower2) + (24678959/10000000000000 : ℝ)*(upper3) + (63044971/25000000000000 : ℝ)*(lower4) + (266091847598183/10000000000000 : ℝ)*(major0) + (266091847598183/10000000000000 : ℝ)*(major1) + (266091847598183/10000000000000 : ℝ)*(major2) + (8168971949/20000000000000 : ℝ)*(sp2) + (232625091/100000000000000 : ℝ)*(sp3) + (723290433875283/20000000000000 : ℝ)*(sp4) + (1808225695793639/50000000000000 : ℝ)*(sp5) + (113012769143443/3125000000000 : ℝ)*(sp6) + (852692225755801/50000000000000 : ℝ)*(sp7) + (1705384684136693/100000000000000 : ℝ)*(f.failure) + (723290433875283/20000000000000 : ℝ)*(f.sum) + (54854244390647/12029000000000000000000000000 : ℝ)*base66 + (13962746968359391/3759062500000000000000000000000 : ℝ)*base68 + (27419194942703141/3759062500000000000000000000000 : ℝ)*base70 + (7014492407266879/939765625000000000000000000000 : ℝ)*base72 + (8630494389617/2405800000000000000000000000 : ℝ)*base74 + (20654997381895657/7518125000000000000000000000000 : ℝ)*base76 + (11639464765604391/3759062500000000000000000000000 : ℝ)*base78 + (285520509295621/939765625000000000000000000000 : ℝ)*base79 + (16144165171923/6014500000000000000000000000 : ℝ)*base82 + (31730107/2500000000000000000000 : ℝ)*base89 + (31730107/2500000000000000000000 : ℝ)*base91 + (31730107/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1375_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (719/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1375_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1375_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1375_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1375_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1375_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2167/512 : ℝ) ≤ p) (hpb : p ≤ (4335/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39007599/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (503/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15979/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1375_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
