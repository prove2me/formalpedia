-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1342_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:15.835301+00:00
-- url     : https://prove2.me/submissions/b8bc60a7-79bc-4c61-8dbe-6c9ba595eba5

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
theorem support_rectangle_w1342_s6_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043967781/10000000000 : ℝ)*x 0 + (5412720133/10000000000 : ℝ)*x 1 + (5244597071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043967781/10000000000 : ℝ)^2151 ≤ (12447326060473/100000000000000 : ℝ)^1639 := by
    have hnat : (2043967781 : ℕ)^2151*100000000000000^1639 ≤ 12447326060473^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043967781 10000000000 12447326060473 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412720133/10000000000 : ℝ)^2151 ≤ (2234129998133/5000000000000 : ℝ)^1639 := by
    have hnat : (5412720133 : ℕ)^2151*5000000000000^1639 ≤ 2234129998133^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412720133 10000000000 2234129998133 5000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244597071/10000000000 : ℝ)^2151 ≤ (42870073959603/100000000000000 : ℝ)^1639 := by
    have hnat : (5244597071 : ℕ)^2151*100000000000000^1639 ≤ 42870073959603^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244597071 10000000000 42870073959603 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043967781/10000000000 : ℝ), (5412720133/10000000000 : ℝ), (5244597071/10000000000 : ℝ)] ![(12447326060473/100000000000000 : ℝ), (2234129998133/5000000000000 : ℝ), (42870073959603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043967781/10000000000 : ℝ)|^2151 ≤ (12447326060473/100000000000000 : ℝ)^1639
        have hw : |(-2043967781/10000000000 : ℝ)|=(2043967781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412720133/10000000000 : ℝ)|^2151 ≤ (2234129998133/5000000000000 : ℝ)^1639
        have hw : |(5412720133/10000000000 : ℝ)|=(5412720133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244597071/10000000000 : ℝ)|^2151 ≤ (42870073959603/100000000000000 : ℝ)^1639
        have hw : |(5244597071/10000000000 : ℝ)|=(5244597071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349001553/10000000000 : ℝ)*x 0 + (-1064813923/5000000000 : ℝ)*x 1 + (52445971/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349001553/10000000000 : ℝ)^2151 ≤ (21996776386267/50000000000000 : ℝ)^1639 := by
    have hnat : (5349001553 : ℕ)^2151*50000000000000^1639 ≤ 21996776386267^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349001553 10000000000 21996776386267 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064813923/5000000000 : ℝ)^2151 ≤ (6568186472669/50000000000000 : ℝ)^1639 := by
    have hnat : (1064813923 : ℕ)^2151*50000000000000^1639 ≤ 6568186472669^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064813923 5000000000 6568186472669 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52445971/100000000 : ℝ)^2151 ≤ (2679379641919/6250000000000 : ℝ)^1639 := by
    have hnat : (52445971 : ℕ)^2151*6250000000000^1639 ≤ 2679379641919^1639*100000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52445971 100000000 2679379641919 6250000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349001553/10000000000 : ℝ), (-1064813923/5000000000 : ℝ), (52445971/100000000 : ℝ)] ![(21996776386267/50000000000000 : ℝ), (6568186472669/50000000000000 : ℝ), (2679379641919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349001553/10000000000 : ℝ)|^2151 ≤ (21996776386267/50000000000000 : ℝ)^1639
        have hw : |(5349001553/10000000000 : ℝ)|=(5349001553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064813923/5000000000 : ℝ)|^2151 ≤ (6568186472669/50000000000000 : ℝ)^1639
        have hw : |(-1064813923/5000000000 : ℝ)|=(1064813923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52445971/100000000 : ℝ)|^2151 ≤ (2679379641919/6250000000000 : ℝ)^1639
        have hw : |(52445971/100000000 : ℝ)|=(52445971/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674500761/5000000000 : ℝ)*x 0 + (5244597113/10000000000 : ℝ)*x 1 + (-2129627869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674500761/5000000000 : ℝ)^2151 ≤ (43993552437923/100000000000000 : ℝ)^1639 := by
    have hnat : (2674500761 : ℕ)^2151*100000000000000^1639 ≤ 43993552437923^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674500761 5000000000 43993552437923 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244597113/10000000000 : ℝ)^2151 ≤ (42870074410163/100000000000000 : ℝ)^1639 := by
    have hnat : (5244597113 : ℕ)^2151*100000000000000^1639 ≤ 42870074410163^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244597113 10000000000 42870074410163 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129627869/10000000000 : ℝ)^2151 ≤ (1313637313153/10000000000000 : ℝ)^1639 := by
    have hnat : (2129627869 : ℕ)^2151*10000000000000^1639 ≤ 1313637313153^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129627869 10000000000 1313637313153 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674500761/5000000000 : ℝ), (5244597113/10000000000 : ℝ), (-2129627869/10000000000 : ℝ)] ![(43993552437923/100000000000000 : ℝ), (42870074410163/100000000000000 : ℝ), (1313637313153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674500761/5000000000 : ℝ)|^2151 ≤ (43993552437923/100000000000000 : ℝ)^1639
        have hw : |(2674500761/5000000000 : ℝ)|=(2674500761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244597113/10000000000 : ℝ)|^2151 ≤ (42870074410163/100000000000000 : ℝ)^1639
        have hw : |(5244597113/10000000000 : ℝ)|=(5244597113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129627869/10000000000 : ℝ)|^2151 ≤ (1313637313153/10000000000000 : ℝ)^1639
        have hw : |(-2129627869/10000000000 : ℝ)|=(2129627869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163308913/5000000000 : ℝ)*x 0 + (129809163/312500000 : ℝ)*x 1 + (2253019537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163308913/5000000000 : ℝ)^2151 ≤ (832581171907/2500000000000 : ℝ)^1639 := by
    have hnat : (2163308913 : ℕ)^2151*2500000000000^1639 ≤ 832581171907^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163308913 5000000000 832581171907 2500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129809163/312500000 : ℝ)^2151 ≤ (15784697760749/50000000000000 : ℝ)^1639 := by
    have hnat : (129809163 : ℕ)^2151*50000000000000^1639 ≤ 15784697760749^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129809163 312500000 15784697760749 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253019537/5000000000 : ℝ)^2151 ≤ (35127357593773/100000000000000 : ℝ)^1639 := by
    have hnat : (2253019537 : ℕ)^2151*100000000000000^1639 ≤ 35127357593773^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253019537 5000000000 35127357593773 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163308913/5000000000 : ℝ), (129809163/312500000 : ℝ), (2253019537/5000000000 : ℝ)] ![(832581171907/2500000000000 : ℝ), (15784697760749/50000000000000 : ℝ), (35127357593773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163308913/5000000000 : ℝ)|^2151 ≤ (832581171907/2500000000000 : ℝ)^1639
        have hw : |(2163308913/5000000000 : ℝ)|=(2163308913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129809163/312500000 : ℝ)|^2151 ≤ (15784697760749/50000000000000 : ℝ)^1639
        have hw : |(129809163/312500000 : ℝ)|=(129809163/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253019537/5000000000 : ℝ)|^2151 ≤ (35127357593773/100000000000000 : ℝ)^1639
        have hw : |(2253019537/5000000000 : ℝ)|=(2253019537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-510994997/2500000000 : ℝ)*x 0 + (655649919/1250000000 : ℝ)*x 1 + (5412114733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510994997/2500000000 : ℝ)^2151 ≤ (6223711810353/50000000000000 : ℝ)^1639 := by
    have hnat : (510994997 : ℕ)^2151*50000000000000^1639 ≤ 6223711810353^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510994997 2500000000 6223711810353 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655649919/1250000000 : ℝ)^2151 ≤ (42876535119873/100000000000000 : ℝ)^1639 := by
    have hnat : (655649919 : ℕ)^2151*100000000000000^1639 ≤ 42876535119873^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655649919 1250000000 42876535119873 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412114733/10000000000 : ℝ)^2151 ≤ (44676041241773/100000000000000 : ℝ)^1639 := by
    have hnat : (5412114733 : ℕ)^2151*100000000000000^1639 ≤ 44676041241773^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412114733 10000000000 44676041241773 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510994997/2500000000 : ℝ), (655649919/1250000000 : ℝ), (5412114733/10000000000 : ℝ)] ![(6223711810353/50000000000000 : ℝ), (42876535119873/100000000000000 : ℝ), (44676041241773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510994997/2500000000 : ℝ)|^2151 ≤ (6223711810353/50000000000000 : ℝ)^1639
        have hw : |(-510994997/2500000000 : ℝ)|=(510994997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655649919/1250000000 : ℝ)|^2151 ≤ (42876535119873/100000000000000 : ℝ)^1639
        have hw : |(655649919/1250000000 : ℝ)|=(655649919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412114733/10000000000 : ℝ)|^2151 ≤ (44676041241773/100000000000000 : ℝ)^1639
        have hw : |(5412114733/10000000000 : ℝ)|=(5412114733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652848381/5000000000 : ℝ)*x 0 + (-981054967/5000000000 : ℝ)*x 1 + (541211511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652848381/5000000000 : ℝ)^2151 ≤ (43526718027471/100000000000000 : ℝ)^1639 := by
    have hnat : (2652848381 : ℕ)^2151*100000000000000^1639 ≤ 43526718027471^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652848381 5000000000 43526718027471 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981054967/5000000000 : ℝ)^2151 ≤ (5898618320387/50000000000000 : ℝ)^1639 := by
    have hnat : (981054967 : ℕ)^2151*50000000000000^1639 ≤ 5898618320387^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981054967 5000000000 5898618320387 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541211511/1000000000 : ℝ)^2151 ≤ (22338022663003/50000000000000 : ℝ)^1639 := by
    have hnat : (541211511 : ℕ)^2151*50000000000000^1639 ≤ 22338022663003^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541211511 1000000000 22338022663003 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652848381/5000000000 : ℝ), (-981054967/5000000000 : ℝ), (541211511/1000000000 : ℝ)] ![(43526718027471/100000000000000 : ℝ), (5898618320387/50000000000000 : ℝ), (22338022663003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652848381/5000000000 : ℝ)|^2151 ≤ (43526718027471/100000000000000 : ℝ)^1639
        have hw : |(2652848381/5000000000 : ℝ)|=(2652848381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-981054967/5000000000 : ℝ)|^2151 ≤ (5898618320387/50000000000000 : ℝ)^1639
        have hw : |(-981054967/5000000000 : ℝ)|=(981054967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541211511/1000000000 : ℝ)|^2151 ≤ (22338022663003/50000000000000 : ℝ)^1639
        have hw : |(541211511/1000000000 : ℝ)|=(541211511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663212113/1250000000 : ℝ)*x 0 + (54121151/100000000 : ℝ)*x 1 + (-1962109753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663212113/1250000000 : ℝ)^2151 ≤ (10881679889079/25000000000000 : ℝ)^1639 := by
    have hnat : (663212113 : ℕ)^2151*25000000000000^1639 ≤ 10881679889079^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663212113 1250000000 10881679889079 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54121151/100000000 : ℝ)^2151 ≤ (44676045217671/100000000000000 : ℝ)^1639 := by
    have hnat : (54121151 : ℕ)^2151*100000000000000^1639 ≤ 44676045217671^1639*100000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54121151 100000000 44676045217671 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1962109753/10000000000 : ℝ)^2151 ≤ (2949308803137/25000000000000 : ℝ)^1639 := by
    have hnat : (1962109753 : ℕ)^2151*25000000000000^1639 ≤ 2949308803137^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962109753 10000000000 2949308803137 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663212113/1250000000 : ℝ), (54121151/100000000 : ℝ), (-1962109753/10000000000 : ℝ)] ![(10881679889079/25000000000000 : ℝ), (44676045217671/100000000000000 : ℝ), (2949308803137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663212113/1250000000 : ℝ)|^2151 ≤ (10881679889079/25000000000000 : ℝ)^1639
        have hw : |(663212113/1250000000 : ℝ)|=(663212113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54121151/100000000 : ℝ)|^2151 ≤ (44676045217671/100000000000000 : ℝ)^1639
        have hw : |(54121151/100000000 : ℝ)|=(54121151/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1962109753/10000000000 : ℝ)|^2151 ≤ (2949308803137/25000000000000 : ℝ)^1639
        have hw : |(-1962109753/10000000000 : ℝ)|=(1962109753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s6_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081660847/2500000000 : ℝ)*x 0 + (2252388921/5000000000 : ℝ)*x 1 + (4155160913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081660847/2500000000 : ℝ)^2151 ≤ (6660701019833/20000000000000 : ℝ)^1639 := by
    have hnat : (1081660847 : ℕ)^2151*20000000000000^1639 ≤ 6660701019833^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081660847 2500000000 6660701019833 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252388921/5000000000 : ℝ)^2151 ≤ (8778613668639/25000000000000 : ℝ)^1639 := by
    have hnat : (2252388921 : ℕ)^2151*25000000000000^1639 ≤ 8778613668639^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252388921 5000000000 8778613668639 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155160913/10000000000 : ℝ)^2151 ≤ (31582040222297/100000000000000 : ℝ)^1639 := by
    have hnat : (4155160913 : ℕ)^2151*100000000000000^1639 ≤ 31582040222297^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155160913 10000000000 31582040222297 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081660847/2500000000 : ℝ), (2252388921/5000000000 : ℝ), (4155160913/10000000000 : ℝ)] ![(6660701019833/20000000000000 : ℝ), (8778613668639/25000000000000 : ℝ), (31582040222297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081660847/2500000000 : ℝ)|^2151 ≤ (6660701019833/20000000000000 : ℝ)^1639
        have hw : |(1081660847/2500000000 : ℝ)|=(1081660847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252388921/5000000000 : ℝ)|^2151 ≤ (8778613668639/25000000000000 : ℝ)^1639
        have hw : |(2252388921/5000000000 : ℝ)|=(2252388921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155160913/10000000000 : ℝ)|^2151 ≤ (31582040222297/100000000000000 : ℝ)^1639
        have hw : |(4155160913/10000000000 : ℝ)|=(4155160913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2787/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2943/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2943/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2943/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11141/100000 : ℝ) ^ (4301/1024 : ℝ) ≤ (9928768485752889/100000000000000000000 : ℝ) := by
    have hpowers : (11141/100000 : ℝ)^4301 ≤ (9928768485752889/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11141 : ℕ)^4301*100000000000000000000^1024 ≤ 9928768485752889^1024*100000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11141 100000 9928768485752889 100000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11141/100000 : ℝ)) (X := (9928768485752889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2943/20000 : ℝ) ^ (4301/1024 : ℝ) ≤ (6389407215593457/20000000000000000000 : ℝ) := by
    have hpowers : (2943/20000 : ℝ)^4301 ≤ (6389407215593457/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2943 : ℕ)^4301*20000000000000000000^1024 ≤ 6389407215593457^1024*20000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2943 20000 6389407215593457 20000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2943/20000 : ℝ)) (X := (6389407215593457/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009928768485752889/50000000000000000000 : ℝ) ≤ (5000236370376487/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (50009928768485752889/50000000000000000000 : ℝ)^1024 ≤ (5000236370376487/5000000000000000 : ℝ)^4301 := by
      have hnat : (50009928768485752889 : ℕ)^1024*5000000000000000^4301 ≤ 5000236370376487^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009928768485752889 50000000000000000000 5000236370376487 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000236370376487/5000000000000000 : ℝ)) (X := (50009928768485752889/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020937902281860087/50000000000000000000 : ℝ) ≤ (625062302349471/625000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (50020937902281860087/50000000000000000000 : ℝ)^1024 ≤ (625062302349471/625000000000000 : ℝ)^4301 := by
      have hnat : (50020937902281860087 : ℕ)^1024*625000000000000^4301 ≤ 625062302349471^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020937902281860087 50000000000000000000 625062302349471 625000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625062302349471/625000000000000 : ℝ)) (X := (50020937902281860087/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006389407215593457/10000000000000000000 : ℝ) ≤ (5000760467215049/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (10006389407215593457/10000000000000000000 : ℝ)^1024 ≤ (5000760467215049/5000000000000000 : ℝ)^4301 := by
      have hnat : (10006389407215593457 : ℕ)^1024*5000000000000000^4301 ≤ 5000760467215049^4301*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006389407215593457 10000000000000000000 5000760467215049 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000760467215049/5000000000000000 : ℝ)) (X := (10006389407215593457/10000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9928768485752889/100000000000000000000 : ℝ) ≤ ((1116562864052946581/1116875000000000000 : ℝ)+2*(262048419281/178700000000000 : ℝ)*(11141/100000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (1116562864052946581/1116875000000000000 : ℝ)+2*(262048419281/178700000000000 : ℝ)*(11141/100000 : ℝ)=(5000236370376487/5000000000000000 : ℝ) by norm_num, show 1+2*(9928768485752889/100000000000000000000 : ℝ)=(50009928768485752889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6389407215593457/20000000000000000000 : ℝ)+(9928768485752889/100000000000000000000 : ℝ) ≤ ((1116562864052946581/1116875000000000000 : ℝ)+(262048419281/178700000000000 : ℝ)*((2943/20000 : ℝ)+(11141/100000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (1116562864052946581/1116875000000000000 : ℝ)+(262048419281/178700000000000 : ℝ)*((2943/20000 : ℝ)+(11141/100000 : ℝ))=(625062302349471/625000000000000 : ℝ) by norm_num, show 1+(6389407215593457/20000000000000000000 : ℝ)+(9928768485752889/100000000000000000000 : ℝ)=(50020937902281860087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6389407215593457/20000000000000000000 : ℝ) ≤ ((1116562864052946581/1116875000000000000 : ℝ)+2*(262048419281/178700000000000 : ℝ)*(2943/20000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (1116562864052946581/1116875000000000000 : ℝ)+2*(262048419281/178700000000000 : ℝ)*(2943/20000 : ℝ)=(5000760467215049/5000000000000000 : ℝ) by norm_num, show 1+2*(6389407215593457/20000000000000000000 : ℝ)=(10006389407215593457/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1116562864052946581/1116875000000000000 : ℝ)*(X 1 0+X 2 0)+(262048419281/178700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (1116562864052946581/1116875000000000000 : ℝ)) (alpha := (262048419281/178700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1116562864052946581/1116875000000000000 : ℝ)*(X 0 1+X 2 1)+(262048419281/178700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (1116562864052946581/1116875000000000000 : ℝ)) (alpha := (262048419281/178700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1116562864052946581/1116875000000000000 : ℝ)*(X 0 2+X 1 2)+(262048419281/178700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (11141/100000 : ℝ)) (hi := (2943/20000 : ℝ)) (c := (1116562864052946581/1116875000000000000 : ℝ)) (alpha := (262048419281/178700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2043967781/10000000000 : ℝ)*X 0 0+(5412720133/10000000000 : ℝ)*X 0 1+(5244597071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349001553/10000000000 : ℝ)*X 1 0+(-1064813923/5000000000 : ℝ)*X 1 1+(52445971/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674500761/5000000000 : ℝ)*X 2 0+(5244597113/10000000000 : ℝ)*X 2 1+(-2129627869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163308913/5000000000 : ℝ)*X 0 0+(129809163/312500000 : ℝ)*X 0 1+(2253019537/5000000000 : ℝ)*X 0 2+(2163308913/5000000000 : ℝ)*X 1 0+(129809163/312500000 : ℝ)*X 1 1+(2253019537/5000000000 : ℝ)*X 1 2+(2163308913/5000000000 : ℝ)*X 2 0+(129809163/312500000 : ℝ)*X 2 1+(2253019537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-510994997/2500000000 : ℝ)*X 0 0+(655649919/1250000000 : ℝ)*X 0 1+(5412114733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652848381/5000000000 : ℝ)*X 1 0+(-981054967/5000000000 : ℝ)*X 1 1+(541211511/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663212113/1250000000 : ℝ)*X 2 0+(54121151/100000000 : ℝ)*X 2 1+(-1962109753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081660847/2500000000 : ℝ)*X 0 0+(2252388921/5000000000 : ℝ)*X 0 1+(4155160913/10000000000 : ℝ)*X 0 2+(1081660847/2500000000 : ℝ)*X 1 0+(2252388921/5000000000 : ℝ)*X 1 1+(4155160913/10000000000 : ℝ)*X 1 2+(1081660847/2500000000 : ℝ)*X 2 0+(2252388921/5000000000 : ℝ)*X 2 1+(4155160913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (321579047586804238994561481/27921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2184175563/100000000000000 : ℝ)*(base19) + (2002880979/100000000000000 : ℝ)*(base23) + (78535347/100000000000000 : ℝ)*(lower2) + (155300431/50000000000000 : ℝ)*(upper3) + (33505441/20000000000000 : ℝ)*(upper5) + (878789301290613/20000000000000 : ℝ)*(major0) + (878789301290613/20000000000000 : ℝ)*(major1) + (2196973253226533/50000000000000 : ℝ)*(major2) + (2974035984005633/50000000000000 : ℝ)*(sp0) + (1189622855078483/20000000000000 : ℝ)*(sp1) + (5948114456686999/100000000000000 : ℝ)*(sp2) + (567950581729899/20000000000000 : ℝ)*(sp3) + (5561444589/12500000000000 : ℝ)*(sp4) + (23260785289/100000000000000 : ℝ)*(sp7) + (88743005294837/3125000000000 : ℝ)*(f.failure) + (5948116459567977/100000000000000 : ℝ)*(f.sum) + (145236162295811/17870000000000000000000000000 : ℝ)*base65 + (7200022092573347/22337500000000000000000000000000 : ℝ)*base68 + (73516602009492881/6980468750000000000000000000000 : ℝ)*base69 + (46075676286560847/22337500000000000000000000000000 : ℝ)*base72 + (100568536029651/17870000000000000000000000000 : ℝ)*base73 + (82922391088782637/13960937500000000000000000000000 : ℝ)*base75 + (105286437269075403/22337500000000000000000000000000 : ℝ)*base77 + (175698779264637903/22337500000000000000000000000000 : ℝ)*base79 + (16731367686081/1787000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (695223/312500000000000000000 : ℝ)*base90 + (695223/312500000000000000000 : ℝ)*base92 + (3820223/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74596160097080249510679831/6980468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1822865941/100000000000000 : ℝ)*(base19) + (2235387797/100000000000000 : ℝ)*(base23) + (304570977/100000000000000 : ℝ)*(upper3) + (35513901/50000000000000 : ℝ)*(lower4) + (162796373/100000000000000 : ℝ)*(upper5) + (4425665488038293/100000000000000 : ℝ)*(major0) + (4425665488038293/100000000000000 : ℝ)*(major1) + (4425665488038293/100000000000000 : ℝ)*(major2) + (22612544663/50000000000000 : ℝ)*(sp1) + (59720453831/100000000000000 : ℝ)*(sp2) + (5991054699716013/100000000000000 : ℝ)*(sp4) + (2995503825880373/50000000000000 : ℝ)*(sp5) + (374437046492149/6250000000000 : ℝ)*(sp6) + (2860275920146857/100000000000000 : ℝ)*(sp7) + (2860275920146857/100000000000000 : ℝ)*(f.failure) + (5991054699716013/100000000000000 : ℝ)*(f.sum) + (2811531918013/8935000000000000000000000000 : ℝ)*base65 + (1644961942304617517/111687500000000000000000000000000 : ℝ)*base68 + (474762169842117517/111687500000000000000000000000000 : ℝ)*base70 + (1834941606480367517/111687500000000000000000000000000 : ℝ)*base72 + (11551424023543/8935000000000000000000000000 : ℝ)*base73 + (302727227464319983/111687500000000000000000000000000 : ℝ)*base75 + (462839469352617517/111687500000000000000000000000000 : ℝ)*base78 + (448829552751430017/111687500000000000000000000000000 : ℝ)*base80 + (31630181792083/8935000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1094197/10000000000000000000000 : ℝ)*base89 + (1094197/10000000000000000000000 : ℝ)*base91 + (1094197/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1342_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1342_s7_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043973229/10000000000 : ℝ)*x 0 + (5412662199/10000000000 : ℝ)*x 1 + (1024346/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043973229/10000000000 : ℝ)^2151 ≤ (12447369601709/100000000000000 : ℝ)^1639 := by
    have hnat : (2043973229 : ℕ)^2151*100000000000000^1639 ≤ 12447369601709^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043973229 10000000000 12447369601709 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412662199/10000000000 : ℝ)^2151 ≤ (44681972313273/100000000000000 : ℝ)^1639 := by
    have hnat : (5412662199 : ℕ)^2151*100000000000000^1639 ≤ 44681972313273^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412662199 10000000000 44681972313273 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024346/1953125 : ℝ)^2151 ≤ (21435329034487/50000000000000 : ℝ)^1639 := by
    have hnat : (1024346 : ℕ)^2151*50000000000000^1639 ≤ 21435329034487^1639*1953125^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024346 1953125 21435329034487 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043973229/10000000000 : ℝ), (5412662199/10000000000 : ℝ), (1024346/1953125 : ℝ)] ![(12447369601709/100000000000000 : ℝ), (44681972313273/100000000000000 : ℝ), (21435329034487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043973229/10000000000 : ℝ)|^2151 ≤ (12447369601709/100000000000000 : ℝ)^1639
        have hw : |(-2043973229/10000000000 : ℝ)|=(2043973229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412662199/10000000000 : ℝ)|^2151 ≤ (44681972313273/100000000000000 : ℝ)^1639
        have hw : |(5412662199/10000000000 : ℝ)|=(5412662199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024346/1953125 : ℝ)|^2151 ≤ (21435329034487/50000000000000 : ℝ)^1639
        have hw : |(1024346/1953125 : ℝ)|=(1024346/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674493243/5000000000 : ℝ)*x 0 + (-133098501/625000000 : ℝ)*x 1 + (1311162843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674493243/5000000000 : ℝ)^2151 ≤ (43993390141147/100000000000000 : ℝ)^1639 := by
    have hnat : (2674493243 : ℕ)^2151*100000000000000^1639 ≤ 43993390141147^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674493243 5000000000 43993390141147 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133098501/625000000 : ℝ)^2151 ≤ (13135953367281/100000000000000 : ℝ)^1639 := by
    have hnat : (133098501 : ℕ)^2151*100000000000000^1639 ≤ 13135953367281^1639*625000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133098501 625000000 13135953367281 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311162843/2500000000 : ℝ)^2151 ≤ (4186587547/9765625000 : ℝ)^1639 := by
    have hnat : (1311162843 : ℕ)^2151*9765625000^1639 ≤ 4186587547^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311162843 2500000000 4186587547 9765625000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674493243/5000000000 : ℝ), (-133098501/625000000 : ℝ), (1311162843/2500000000 : ℝ)] ![(43993390141147/100000000000000 : ℝ), (13135953367281/100000000000000 : ℝ), (4186587547/9765625000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674493243/5000000000 : ℝ)|^2151 ≤ (43993390141147/100000000000000 : ℝ)^1639
        have hw : |(2674493243/5000000000 : ℝ)|=(2674493243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133098501/625000000 : ℝ)|^2151 ≤ (13135953367281/100000000000000 : ℝ)^1639
        have hw : |(-133098501/625000000 : ℝ)|=(133098501/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311162843/2500000000 : ℝ)|^2151 ≤ (4186587547/9765625000 : ℝ)^1639
        have hw : |(1311162843/2500000000 : ℝ)|=(1311162843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069797479/2000000000 : ℝ)*x 0 + (2622325541/5000000000 : ℝ)*x 1 + (-2129575187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069797479/2000000000 : ℝ)^2151 ≤ (43993399952779/100000000000000 : ℝ)^1639 := by
    have hnat : (1069797479 : ℕ)^2151*100000000000000^1639 ≤ 43993399952779^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069797479 2000000000 43993399952779 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622325541/5000000000 : ℝ)^2151 ≤ (42870653370259/100000000000000 : ℝ)^1639 := by
    have hnat : (2622325541 : ℕ)^2151*100000000000000^1639 ≤ 42870653370259^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622325541 5000000000 42870653370259 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129575187/10000000000 : ℝ)^2151 ≤ (3283986664081/25000000000000 : ℝ)^1639 := by
    have hnat : (2129575187 : ℕ)^2151*25000000000000^1639 ≤ 3283986664081^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129575187 10000000000 3283986664081 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069797479/2000000000 : ℝ), (2622325541/5000000000 : ℝ), (-2129575187/10000000000 : ℝ)] ![(43993399952779/100000000000000 : ℝ), (42870653370259/100000000000000 : ℝ), (3283986664081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069797479/2000000000 : ℝ)|^2151 ≤ (43993399952779/100000000000000 : ℝ)^1639
        have hw : |(1069797479/2000000000 : ℝ)|=(1069797479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622325541/5000000000 : ℝ)|^2151 ≤ (42870653370259/100000000000000 : ℝ)^1639
        have hw : |(2622325541/5000000000 : ℝ)|=(2622325541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2129575187/10000000000 : ℝ)|^2151 ≤ (3283986664081/25000000000000 : ℝ)^1639
        have hw : |(-2129575187/10000000000 : ℝ)|=(2129575187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163310897/5000000000 : ℝ)*x 0 + (4154010691/10000000000 : ℝ)*x 1 + (1126480157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163310897/5000000000 : ℝ)^2151 ≤ (6660657392059/20000000000000 : ℝ)^1639 := by
    have hnat : (2163310897 : ℕ)^2151*20000000000000^1639 ≤ 6660657392059^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163310897 5000000000 6660657392059 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154010691/10000000000 : ℝ)^2151 ≤ (15785283615251/50000000000000 : ℝ)^1639 := by
    have hnat : (4154010691 : ℕ)^2151*50000000000000^1639 ≤ 15785283615251^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154010691 10000000000 15785283615251 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126480157/2500000000 : ℝ)^2151 ≤ (17563072897371/50000000000000 : ℝ)^1639 := by
    have hnat : (1126480157 : ℕ)^2151*50000000000000^1639 ≤ 17563072897371^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126480157 2500000000 17563072897371 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163310897/5000000000 : ℝ), (4154010691/10000000000 : ℝ), (1126480157/2500000000 : ℝ)] ![(6660657392059/20000000000000 : ℝ), (15785283615251/50000000000000 : ℝ), (17563072897371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163310897/5000000000 : ℝ)|^2151 ≤ (6660657392059/20000000000000 : ℝ)^1639
        have hw : |(2163310897/5000000000 : ℝ)|=(2163310897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154010691/10000000000 : ℝ)|^2151 ≤ (15785283615251/50000000000000 : ℝ)^1639
        have hw : |(4154010691/10000000000 : ℝ)|=(4154010691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126480157/2500000000 : ℝ)|^2151 ≤ (17563072897371/50000000000000 : ℝ)^1639
        have hw : |(1126480157/2500000000 : ℝ)|=(1126480157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043985359/10000000000 : ℝ)*x 0 + (1049050621/2000000000 : ℝ)*x 1 + (5412057541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043985359/10000000000 : ℝ)^2151 ≤ (6223733273313/50000000000000 : ℝ)^1639 := by
    have hnat : (2043985359 : ℕ)^2151*50000000000000^1639 ≤ 6223733273313^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043985359 10000000000 6223733273313 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049050621/2000000000 : ℝ)^2151 ≤ (42877111783479/100000000000000 : ℝ)^1639 := by
    have hnat : (1049050621 : ℕ)^2151*100000000000000^1639 ≤ 42877111783479^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049050621 2000000000 42877111783479 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412057541/10000000000 : ℝ)^2151 ≤ (22337710826377/50000000000000 : ℝ)^1639 := by
    have hnat : (5412057541 : ℕ)^2151*50000000000000^1639 ≤ 22337710826377^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412057541 10000000000 22337710826377 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043985359/10000000000 : ℝ), (1049050621/2000000000 : ℝ), (5412057541/10000000000 : ℝ)] ![(6223733273313/50000000000000 : ℝ), (42877111783479/100000000000000 : ℝ), (22337710826377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043985359/10000000000 : ℝ)|^2151 ≤ (6223733273313/50000000000000 : ℝ)^1639
        have hw : |(-2043985359/10000000000 : ℝ)|=(2043985359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049050621/2000000000 : ℝ)|^2151 ≤ (42877111783479/100000000000000 : ℝ)^1639
        have hw : |(1049050621/2000000000 : ℝ)|=(1049050621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412057541/10000000000 : ℝ)|^2151 ≤ (22337710826377/50000000000000 : ℝ)^1639
        have hw : |(5412057541/10000000000 : ℝ)|=(5412057541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305711183/10000000000 : ℝ)*x 0 + (-1962168443/10000000000 : ℝ)*x 1 + (5412058161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305711183/10000000000 : ℝ)^2151 ≤ (2176343664569/5000000000000 : ℝ)^1639 := by
    have hnat : (5305711183 : ℕ)^2151*5000000000000^1639 ≤ 2176343664569^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305711183 10000000000 2176343664569 5000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1962168443/10000000000 : ℝ)^2151 ≤ (11797698322951/100000000000000 : ℝ)^1639 := by
    have hnat : (1962168443 : ℕ)^2151*100000000000000^1639 ≤ 11797698322951^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962168443 10000000000 11797698322951 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412058161/10000000000 : ℝ)^2151 ≤ (44675428369507/100000000000000 : ℝ)^1639 := by
    have hnat : (5412058161 : ℕ)^2151*100000000000000^1639 ≤ 44675428369507^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412058161 10000000000 44675428369507 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305711183/10000000000 : ℝ), (-1962168443/10000000000 : ℝ), (5412058161/10000000000 : ℝ)] ![(2176343664569/5000000000000 : ℝ), (11797698322951/100000000000000 : ℝ), (44675428369507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305711183/10000000000 : ℝ)|^2151 ≤ (2176343664569/5000000000000 : ℝ)^1639
        have hw : |(5305711183/10000000000 : ℝ)|=(5305711183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1962168443/10000000000 : ℝ)|^2151 ≤ (11797698322951/100000000000000 : ℝ)^1639
        have hw : |(-1962168443/10000000000 : ℝ)|=(1962168443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412058161/10000000000 : ℝ)|^2151 ≤ (44675428369507/100000000000000 : ℝ)^1639
        have hw : |(5412058161/10000000000 : ℝ)|=(5412058161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652855643/5000000000 : ℝ)*x 0 + (676507253/1250000000 : ℝ)*x 1 + (-196216849/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652855643/5000000000 : ℝ)^2151 ≤ (10881718600083/25000000000000 : ℝ)^1639 := by
    have hnat : (2652855643 : ℕ)^2151*25000000000000^1639 ≤ 10881718600083^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652855643 5000000000 10881718600083 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676507253/1250000000 : ℝ)^2151 ≤ (44675426885321/100000000000000 : ℝ)^1639 := by
    have hnat : (676507253 : ℕ)^2151*100000000000000^1639 ≤ 44675426885321^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676507253 1250000000 44675426885321 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196216849/1000000000 : ℝ)^2151 ≤ (589884934691/5000000000000 : ℝ)^1639 := by
    have hnat : (196216849 : ℕ)^2151*5000000000000^1639 ≤ 589884934691^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196216849 1000000000 589884934691 5000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652855643/5000000000 : ℝ), (676507253/1250000000 : ℝ), (-196216849/1000000000 : ℝ)] ![(10881718600083/25000000000000 : ℝ), (44675426885321/100000000000000 : ℝ), (589884934691/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652855643/5000000000 : ℝ)|^2151 ≤ (10881718600083/25000000000000 : ℝ)^1639
        have hw : |(2652855643/5000000000 : ℝ)|=(2652855643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676507253/1250000000 : ℝ)|^2151 ≤ (44675426885321/100000000000000 : ℝ)^1639
        have hw : |(676507253/1250000000 : ℝ)|=(676507253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196216849/1000000000 : ℝ)|^2151 ≤ (589884934691/5000000000000 : ℝ)^1639
        have hw : |(-196216849/1000000000 : ℝ)|=(196216849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_s7_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4326647673/10000000000 : ℝ)*x 0 + (900932303/2000000000 : ℝ)*x 1 + (129852371/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326647673/10000000000 : ℝ)^2151 ≤ (16651774192769/50000000000000 : ℝ)^1639 := by
    have hnat : (4326647673 : ℕ)^2151*50000000000000^1639 ≤ 16651774192769^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326647673 10000000000 16651774192769 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900932303/2000000000 : ℝ)^2151 ≤ (35113264658603/100000000000000 : ℝ)^1639 := by
    have hnat : (900932303 : ℕ)^2151*100000000000000^1639 ≤ 35113264658603^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900932303 2000000000 35113264658603 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129852371/312500000 : ℝ)^2151 ≤ (31583186945621/100000000000000 : ℝ)^1639 := by
    have hnat : (129852371 : ℕ)^2151*100000000000000^1639 ≤ 31583186945621^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129852371 312500000 31583186945621 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326647673/10000000000 : ℝ), (900932303/2000000000 : ℝ), (129852371/312500000 : ℝ)] ![(16651774192769/50000000000000 : ℝ), (35113264658603/100000000000000 : ℝ), (31583186945621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326647673/10000000000 : ℝ)|^2151 ≤ (16651774192769/50000000000000 : ℝ)^1639
        have hw : |(4326647673/10000000000 : ℝ)|=(4326647673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900932303/2000000000 : ℝ)|^2151 ≤ (35113264658603/100000000000000 : ℝ)^1639
        have hw : |(900932303/2000000000 : ℝ)|=(900932303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129852371/312500000 : ℝ)|^2151 ≤ (31583186945621/100000000000000 : ℝ)^1639
        have hw : |(129852371/312500000 : ℝ)|=(129852371/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (223/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2787/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2787/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2787/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2787/25000 : ℝ) ^ (4301/1024 : ℝ) ≤ (4977498549780907/50000000000000000000 : ℝ) := by
    have hpowers : (2787/25000 : ℝ)^4301 ≤ (4977498549780907/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2787 : ℕ)^4301*50000000000000000000^1024 ≤ 4977498549780907^1024*25000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2787 25000 4977498549780907 50000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2787/25000 : ℝ)) (X := (4977498549780907/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3677/25000 : ℝ) ^ (4301/1024 : ℝ) ≤ (15941626369711889/50000000000000000000 : ℝ) := by
    have hpowers : (3677/25000 : ℝ)^4301 ≤ (15941626369711889/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3677 : ℕ)^4301*50000000000000000000^1024 ≤ 15941626369711889^1024*25000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3677 25000 15941626369711889 50000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3677/25000 : ℝ)) (X := (15941626369711889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004977498549780907/25000000000000000000 : ℝ) ≤ (10000473989487329/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (25004977498549780907/25000000000000000000 : ℝ)^1024 ≤ (10000473989487329/10000000000000000 : ℝ)^4301 := by
      have hnat : (25004977498549780907 : ℕ)^1024*10000000000000000^4301 ≤ 10000473989487329^4301*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004977498549780907 25000000000000000000 10000473989487329 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000473989487329/10000000000000000 : ℝ)) (X := (25004977498549780907/25000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505229781229873199/12500000000000000000 : ℝ) ≤ (5000497971879023/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (12505229781229873199/12500000000000000000 : ℝ)^1024 ≤ (5000497971879023/5000000000000000 : ℝ)^4301 := by
      have hnat : (12505229781229873199 : ℕ)^1024*5000000000000000^4301 ≤ 5000497971879023^4301*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505229781229873199 12500000000000000000 5000497971879023 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000497971879023/5000000000000000 : ℝ)) (X := (12505229781229873199/12500000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015941626369711889/25000000000000000000 : ℝ) ≤ (10001517898028763/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (25015941626369711889/25000000000000000000 : ℝ)^1024 ≤ (10001517898028763/10000000000000000 : ℝ)^4301 := by
      have hnat : (25015941626369711889 : ℕ)^1024*10000000000000000^4301 ≤ 10001517898028763^4301*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015941626369711889 25000000000000000000 10001517898028763 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001517898028763/10000000000000000 : ℝ)) (X := (25015941626369711889/25000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4977498549780907/50000000000000000000 : ℝ) ≤ ((2224378119384686563/2225000000000000000 : ℝ)+2*(521954270717/356000000000000 : ℝ)*(2787/25000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (2224378119384686563/2225000000000000000 : ℝ)+2*(521954270717/356000000000000 : ℝ)*(2787/25000 : ℝ)=(10000473989487329/10000000000000000 : ℝ) by norm_num, show 1+2*(4977498549780907/50000000000000000000 : ℝ)=(25004977498549780907/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15941626369711889/50000000000000000000 : ℝ)+(4977498549780907/50000000000000000000 : ℝ) ≤ ((2224378119384686563/2225000000000000000 : ℝ)+(521954270717/356000000000000 : ℝ)*((3677/25000 : ℝ)+(2787/25000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (2224378119384686563/2225000000000000000 : ℝ)+(521954270717/356000000000000 : ℝ)*((3677/25000 : ℝ)+(2787/25000 : ℝ))=(5000497971879023/5000000000000000 : ℝ) by norm_num, show 1+(15941626369711889/50000000000000000000 : ℝ)+(4977498549780907/50000000000000000000 : ℝ)=(12505229781229873199/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15941626369711889/50000000000000000000 : ℝ) ≤ ((2224378119384686563/2225000000000000000 : ℝ)+2*(521954270717/356000000000000 : ℝ)*(3677/25000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (2224378119384686563/2225000000000000000 : ℝ)+2*(521954270717/356000000000000 : ℝ)*(3677/25000 : ℝ)=(10001517898028763/10000000000000000 : ℝ) by norm_num, show 1+2*(15941626369711889/50000000000000000000 : ℝ)=(25015941626369711889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2224378119384686563/2225000000000000000 : ℝ)*(X 1 0+X 2 0)+(521954270717/356000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (2224378119384686563/2225000000000000000 : ℝ)) (alpha := (521954270717/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2224378119384686563/2225000000000000000 : ℝ)*(X 0 1+X 2 1)+(521954270717/356000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (2224378119384686563/2225000000000000000 : ℝ)) (alpha := (521954270717/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2224378119384686563/2225000000000000000 : ℝ)*(X 0 2+X 1 2)+(521954270717/356000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (2787/25000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (2224378119384686563/2225000000000000000 : ℝ)) (alpha := (521954270717/356000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2043973229/10000000000 : ℝ)*X 0 0+(5412662199/10000000000 : ℝ)*X 0 1+(1024346/1953125 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674493243/5000000000 : ℝ)*X 1 0+(-133098501/625000000 : ℝ)*X 1 1+(1311162843/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069797479/2000000000 : ℝ)*X 2 0+(2622325541/5000000000 : ℝ)*X 2 1+(-2129575187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163310897/5000000000 : ℝ)*X 0 0+(4154010691/10000000000 : ℝ)*X 0 1+(1126480157/2500000000 : ℝ)*X 0 2+(2163310897/5000000000 : ℝ)*X 1 0+(4154010691/10000000000 : ℝ)*X 1 1+(1126480157/2500000000 : ℝ)*X 1 2+(2163310897/5000000000 : ℝ)*X 2 0+(4154010691/10000000000 : ℝ)*X 2 1+(1126480157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2043985359/10000000000 : ℝ)*X 0 0+(1049050621/2000000000 : ℝ)*X 0 1+(5412057541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305711183/10000000000 : ℝ)*X 1 0+(-1962168443/10000000000 : ℝ)*X 1 1+(5412058161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652855643/5000000000 : ℝ)*X 2 0+(676507253/1250000000 : ℝ)*X 2 1+(-196216849/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326647673/10000000000 : ℝ)*X 0 0+(900932303/2000000000 : ℝ)*X 0 1+(129852371/312500000 : ℝ)*X 0 2+(4326647673/10000000000 : ℝ)*X 1 0+(900932303/2000000000 : ℝ)*X 1 1+(129852371/312500000 : ℝ)*X 1 2+(4326647673/10000000000 : ℝ)*X 2 0+(900932303/2000000000 : ℝ)*X 2 1+(129852371/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10571252889321077219289/2225000000000000000000000000 : ℝ) := by norm_num
    linear_combination (111331297/25000000000000 : ℝ)*(base23) + (254299791/100000000000000 : ℝ)*(lower2) + (124078407/100000000000000 : ℝ)*(upper4) + (6561037/6250000000000 : ℝ)*(upper5) + (137400603005803/3125000000000 : ℝ)*(major0) + (137400603005803/3125000000000 : ℝ)*(major1) + (137400603005803/3125000000000 : ℝ)*(major2) + (2975996703150223/50000000000000 : ℝ)*(sp0) + (595198814434259/10000000000000 : ℝ)*(sp1) + (1190401031160723/20000000000000 : ℝ)*(sp2) + (710407943851873/25000000000000 : ℝ)*(sp3) + (6097414179/50000000000000 : ℝ)*(sp4) + (17456786213/100000000000000 : ℝ)*(sp5) + (52873213/5000000000000 : ℝ)*(sp7) + (355204104108969/12500000000000 : ℝ)*(f.failure) + (5952005601128803/100000000000000 : ℝ)*(f.sum) + (326113257519/139062500000000000000000000 : ℝ)*base65 + (32453226343931161/6953125000000000000000000000000 : ℝ)*base68 + (62045462667524911/6953125000000000000000000000000 : ℝ)*base70 + (1520464458177101/108642578125000000000000000000 : ℝ)*base71 + (858867795579/2225000000000000000000000000 : ℝ)*base73 + (30241694364035893/3476562500000000000000000000000 : ℝ)*base76 + (24625299992370357/3476562500000000000000000000000 : ℝ)*base77 + (66651965167475089/6953125000000000000000000000000 : ℝ)*base79 + (1352983295529/2225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (7101749/1250000000000000000000 : ℝ)*base89 + (7101749/1250000000000000000000 : ℝ)*base91 + (7101749/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2366716209321883539567/890000000000000000000000000 : ℝ) := by norm_num
    linear_combination (291145557/100000000000000 : ℝ)*(base19) + (983678249/100000000000000 : ℝ)*(base23) + (192682497/50000000000000 : ℝ)*(lower1) + (29975417/25000000000000 : ℝ)*(upper3) + (125861953/50000000000000 : ℝ)*(lower4) + (221429448296411/5000000000000 : ℝ)*(major0) + (221429448296411/5000000000000 : ℝ)*(major1) + (221429448296411/5000000000000 : ℝ)*(major2) + (12470002463/100000000000000 : ℝ)*(sp2) + (2241439523/50000000000000 : ℝ)*(sp3) + (374688281264899/6250000000000 : ℝ)*(sp4) + (5995012209092827/100000000000000 : ℝ)*(sp5) + (5994999046557671/100000000000000 : ℝ)*(sp6) + (1431080430048973/50000000000000 : ℝ)*(sp7) + (89442666968031/3125000000000 : ℝ)*(f.failure) + (374688281264899/6250000000000 : ℝ)*(f.sum) + (1824500886547/890000000000000000000000000 : ℝ)*base65 + (19594074760880857/11125000000000000000000000000000 : ℝ)*base68 + (85923129769880857/11125000000000000000000000000000 : ℝ)*base70 + (35249046588744143/11125000000000000000000000000000 : ℝ)*base71 + (732575649337/890000000000000000000000000 : ℝ)*base73 + (223284143378255857/11125000000000000000000000000000 : ℝ)*base76 + (277979364582494143/11125000000000000000000000000000 : ℝ)*base77 + (23640626145369143/11125000000000000000000000000000 : ℝ)*base79 + (1168963284877/890000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (215251/312500000000000000000 : ℝ)*base89 + (215251/312500000000000000000 : ℝ)*base91 + (215251/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1342_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2787/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1342_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1342_box_0 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-58647567/312500000 : ℝ)*x 0 + (2694969613/5000000000 : ℝ)*x 1 + (673742377/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58647567/312500000 : ℝ)^2151 ≤ (11128089091969/100000000000000 : ℝ)^1639 := by
    have hnat : (58647567 : ℕ)^2151*100000000000000^1639 ≤ 11128089091969^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58647567 312500000 11128089091969 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694969613/5000000000 : ℝ)^2151 ≤ (5554494572727/12500000000000 : ℝ)^1639 := by
    have hnat : (2694969613 : ℕ)^2151*12500000000000^1639 ≤ 5554494572727^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694969613 5000000000 5554494572727 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673742377/1250000000 : ℝ)^2151 ≤ (8887190861939/20000000000000 : ℝ)^1639 := by
    have hnat : (673742377 : ℕ)^2151*20000000000000^1639 ≤ 8887190861939^1639*1250000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673742377 1250000000 8887190861939 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58647567/312500000 : ℝ), (2694969613/5000000000 : ℝ), (673742377/1250000000 : ℝ)] ![(11128089091969/100000000000000 : ℝ), (5554494572727/12500000000000 : ℝ), (8887190861939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58647567/312500000 : ℝ)|^2151 ≤ (11128089091969/100000000000000 : ℝ)^1639
        have hw : |(-58647567/312500000 : ℝ)|=(58647567/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694969613/5000000000 : ℝ)|^2151 ≤ (5554494572727/12500000000000 : ℝ)^1639
        have hw : |(2694969613/5000000000 : ℝ)|=(2694969613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673742377/1250000000 : ℝ)|^2151 ≤ (8887190861939/20000000000000 : ℝ)^1639
        have hw : |(673742377/1250000000 : ℝ)|=(673742377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_1 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (330322831/625000000 : ℝ)*x 0 + (-126266637/625000000 : ℝ)*x 1 + (84217801/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330322831/625000000 : ℝ)^2151 ≤ (43305799517563/100000000000000 : ℝ)^1639 := by
    have hnat : (330322831 : ℕ)^2151*100000000000000^1639 ≤ 43305799517563^1639*625000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330322831 625000000 43305799517563 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126266637/625000000 : ℝ)^2151 ≤ (2451648695043/20000000000000 : ℝ)^1639 := by
    have hnat : (126266637 : ℕ)^2151*20000000000000^1639 ≤ 2451648695043^1639*625000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126266637 625000000 2451648695043 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84217801/156250000 : ℝ)^2151 ≤ (44435956992961/100000000000000 : ℝ)^1639 := by
    have hnat : (84217801 : ℕ)^2151*100000000000000^1639 ≤ 44435956992961^1639*156250000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84217801 156250000 44435956992961 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330322831/625000000 : ℝ), (-126266637/625000000 : ℝ), (84217801/156250000 : ℝ)] ![(43305799517563/100000000000000 : ℝ), (2451648695043/20000000000000 : ℝ), (44435956992961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330322831/625000000 : ℝ)|^2151 ≤ (43305799517563/100000000000000 : ℝ)^1639
        have hw : |(330322831/625000000 : ℝ)|=(330322831/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126266637/625000000 : ℝ)|^2151 ≤ (2451648695043/20000000000000 : ℝ)^1639
        have hw : |(-126266637/625000000 : ℝ)|=(126266637/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84217801/156250000 : ℝ)|^2151 ≤ (44435956992961/100000000000000 : ℝ)^1639
        have hw : |(84217801/156250000 : ℝ)|=(84217801/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_2 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642582539/5000000000 : ℝ)*x 0 + (5389939371/10000000000 : ℝ)*x 1 + (-2020266341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642582539/5000000000 : ℝ)^2151 ≤ (8661159434661/20000000000000 : ℝ)^1639 := by
    have hnat : (2642582539 : ℕ)^2151*20000000000000^1639 ≤ 8661159434661^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642582539 5000000000 8661159434661 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389939371/10000000000 : ℝ)^2151 ≤ (44435958150661/100000000000000 : ℝ)^1639 := by
    have hnat : (5389939371 : ℕ)^2151*100000000000000^1639 ≤ 44435958150661^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389939371 10000000000 44435958150661 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2020266341/10000000000 : ℝ)^2151 ≤ (6129122330857/50000000000000 : ℝ)^1639 := by
    have hnat : (2020266341 : ℕ)^2151*50000000000000^1639 ≤ 6129122330857^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020266341 10000000000 6129122330857 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642582539/5000000000 : ℝ), (5389939371/10000000000 : ℝ), (-2020266341/10000000000 : ℝ)] ![(8661159434661/20000000000000 : ℝ), (44435958150661/100000000000000 : ℝ), (6129122330857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642582539/5000000000 : ℝ)|^2151 ≤ (8661159434661/20000000000000 : ℝ)^1639
        have hw : |(2642582539/5000000000 : ℝ)|=(2642582539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389939371/10000000000 : ℝ)|^2151 ≤ (44435958150661/100000000000000 : ℝ)^1639
        have hw : |(5389939371/10000000000 : ℝ)|=(5389939371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2020266341/10000000000 : ℝ)|^2151 ≤ (6129122330857/50000000000000 : ℝ)^1639
        have hw : |(-2020266341/10000000000 : ℝ)|=(2020266341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_3 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4474808611/10000000000 : ℝ)*x 0 + (2128208937/5000000000 : ℝ)*x 1 + (4256418169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4474808611/10000000000 : ℝ)^2151 ≤ (34808189652833/100000000000000 : ℝ)^1639 := by
    have hnat : (4474808611 : ℕ)^2151*100000000000000^1639 ≤ 34808189652833^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474808611 10000000000 34808189652833 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128208937/5000000000 : ℝ)^2151 ≤ (32595903690031/100000000000000 : ℝ)^1639 := by
    have hnat : (2128208937 : ℕ)^2151*100000000000000^1639 ≤ 32595903690031^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128208937 5000000000 32595903690031 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4256418169/10000000000 : ℝ)^2151 ≤ (16297953327439/50000000000000 : ℝ)^1639 := by
    have hnat : (4256418169 : ℕ)^2151*50000000000000^1639 ≤ 16297953327439^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256418169 10000000000 16297953327439 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4474808611/10000000000 : ℝ), (2128208937/5000000000 : ℝ), (4256418169/10000000000 : ℝ)] ![(34808189652833/100000000000000 : ℝ), (32595903690031/100000000000000 : ℝ), (16297953327439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4474808611/10000000000 : ℝ)|^2151 ≤ (34808189652833/100000000000000 : ℝ)^1639
        have hw : |(4474808611/10000000000 : ℝ)|=(4474808611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2128208937/5000000000 : ℝ)|^2151 ≤ (32595903690031/100000000000000 : ℝ)^1639
        have hw : |(2128208937/5000000000 : ℝ)|=(2128208937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4256418169/10000000000 : ℝ)|^2151 ≤ (16297953327439/50000000000000 : ℝ)^1639
        have hw : |(4256418169/10000000000 : ℝ)|=(4256418169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_4 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106988287/5000000000 : ℝ)*x 0 + (164529007/312500000 : ℝ)*x 1 + (5264927303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106988287/5000000000 : ℝ)^2151 ≤ (1382338812449/10000000000000 : ℝ)^1639 := by
    have hnat : (1106988287 : ℕ)^2151*10000000000000^1639 ≤ 1382338812449^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106988287 5000000000 1382338812449 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164529007/312500000 : ℝ)^2151 ≤ (10772077719519/25000000000000 : ℝ)^1639 := by
    have hnat : (164529007 : ℕ)^2151*25000000000000^1639 ≤ 10772077719519^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164529007 312500000 10772077719519 25000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264927303/10000000000 : ℝ)^2151 ≤ (8617660197197/20000000000000 : ℝ)^1639 := by
    have hnat : (5264927303 : ℕ)^2151*20000000000000^1639 ≤ 8617660197197^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264927303 10000000000 8617660197197 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106988287/5000000000 : ℝ), (164529007/312500000 : ℝ), (5264927303/10000000000 : ℝ)] ![(1382338812449/10000000000000 : ℝ), (10772077719519/25000000000000 : ℝ), (8617660197197/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106988287/5000000000 : ℝ)|^2151 ≤ (1382338812449/10000000000000 : ℝ)^1639
        have hw : |(-1106988287/5000000000 : ℝ)|=(1106988287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164529007/312500000 : ℝ)|^2151 ≤ (10772077719519/25000000000000 : ℝ)^1639
        have hw : |(164529007/312500000 : ℝ)|=(164529007/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264927303/10000000000 : ℝ)|^2151 ≤ (8617660197197/20000000000000 : ℝ)^1639
        have hw : |(5264927303/10000000000 : ℝ)|=(5264927303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_5 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686485873/5000000000 : ℝ)*x 0 + (-414085861/2000000000 : ℝ)*x 1 + (2632463511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686485873/5000000000 : ℝ)^2151 ≤ (35401972143/80000000000 : ℝ)^1639 := by
    have hnat : (2686485873 : ℕ)^2151*80000000000^1639 ≤ 35401972143^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686485873 5000000000 35401972143 80000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414085861/2000000000 : ℝ)^2151 ≤ (6329618418317/50000000000000 : ℝ)^1639 := by
    have hnat : (414085861 : ℕ)^2151*50000000000000^1639 ≤ 6329618418317^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414085861 2000000000 6329618418317 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632463511/5000000000 : ℝ)^2151 ≤ (21544148983939/50000000000000 : ℝ)^1639 := by
    have hnat : (2632463511 : ℕ)^2151*50000000000000^1639 ≤ 21544148983939^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632463511 5000000000 21544148983939 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686485873/5000000000 : ℝ), (-414085861/2000000000 : ℝ), (2632463511/5000000000 : ℝ)] ![(35401972143/80000000000 : ℝ), (6329618418317/50000000000000 : ℝ), (21544148983939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686485873/5000000000 : ℝ)|^2151 ≤ (35401972143/80000000000 : ℝ)^1639
        have hw : |(2686485873/5000000000 : ℝ)|=(2686485873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414085861/2000000000 : ℝ)|^2151 ≤ (6329618418317/50000000000000 : ℝ)^1639
        have hw : |(-414085861/2000000000 : ℝ)|=(414085861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632463511/5000000000 : ℝ)|^2151 ≤ (21544148983939/50000000000000 : ℝ)^1639
        have hw : |(2632463511/5000000000 : ℝ)|=(2632463511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_6 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686485537/5000000000 : ℝ)*x 0 + (2632463667/5000000000 : ℝ)*x 1 + (-64700931/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686485537/5000000000 : ℝ)^2151 ≤ (44252457915121/100000000000000 : ℝ)^1639 := by
    have hnat : (2686485537 : ℕ)^2151*100000000000000^1639 ≤ 44252457915121^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686485537 5000000000 44252457915121 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632463667/5000000000 : ℝ)^2151 ≤ (1346509416217/3125000000000 : ℝ)^1639 := by
    have hnat : (2632463667 : ℕ)^2151*3125000000000^1639 ≤ 1346509416217^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632463667 5000000000 1346509416217 3125000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64700931/312500000 : ℝ)^2151 ≤ (12659240744481/100000000000000 : ℝ)^1639 := by
    have hnat : (64700931 : ℕ)^2151*100000000000000^1639 ≤ 12659240744481^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64700931 312500000 12659240744481 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686485537/5000000000 : ℝ), (2632463667/5000000000 : ℝ), (-64700931/312500000 : ℝ)] ![(44252457915121/100000000000000 : ℝ), (1346509416217/3125000000000 : ℝ), (12659240744481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686485537/5000000000 : ℝ)|^2151 ≤ (44252457915121/100000000000000 : ℝ)^1639
        have hw : |(2686485537/5000000000 : ℝ)|=(2686485537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632463667/5000000000 : ℝ)|^2151 ≤ (1346509416217/3125000000000 : ℝ)^1639
        have hw : |(2632463667/5000000000 : ℝ)|=(2632463667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64700931/312500000 : ℝ)|^2151 ≤ (12659240744481/100000000000000 : ℝ)^1639
        have hw : |(-64700931/312500000 : ℝ)|=(64700931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_7 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1044377389/2500000000 : ℝ)*x 0 + (2202506777/5000000000 : ℝ)*x 1 + (88100287/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044377389/2500000000 : ℝ)^2151 ≤ (1272206217627/4000000000000 : ℝ)^1639 := by
    have hnat : (1044377389 : ℕ)^2151*4000000000000^1639 ≤ 1272206217627^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044377389 2500000000 1272206217627 4000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202506777/5000000000 : ℝ)^2151 ≤ (1363896728907/4000000000000 : ℝ)^1639 := by
    have hnat : (2202506777 : ℕ)^2151*4000000000000^1639 ≤ 1363896728907^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202506777 5000000000 1363896728907 4000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88100287/200000000 : ℝ)^2151 ≤ (6819485261791/20000000000000 : ℝ)^1639 := by
    have hnat : (88100287 : ℕ)^2151*20000000000000^1639 ≤ 6819485261791^1639*200000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88100287 200000000 6819485261791 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044377389/2500000000 : ℝ), (2202506777/5000000000 : ℝ), (88100287/200000000 : ℝ)] ![(1272206217627/4000000000000 : ℝ), (1363896728907/4000000000000 : ℝ), (6819485261791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044377389/2500000000 : ℝ)|^2151 ≤ (1272206217627/4000000000000 : ℝ)^1639
        have hw : |(1044377389/2500000000 : ℝ)|=(1044377389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2202506777/5000000000 : ℝ)|^2151 ≤ (1363896728907/4000000000000 : ℝ)^1639
        have hw : |(2202506777/5000000000 : ℝ)|=(2202506777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88100287/200000000 : ℝ)|^2151 ≤ (6819485261791/20000000000000 : ℝ)^1639
        have hw : |(88100287/200000000 : ℝ)|=(88100287/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_8 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143153487/10000000000 : ℝ)*x 0 + (5178866081/10000000000 : ℝ)*x 1 + (168873709/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143153487/10000000000 : ℝ)^2151 ≤ (1324597559439/10000000000000 : ℝ)^1639 := by
    have hnat : (2143153487 : ℕ)^2151*10000000000000^1639 ≤ 1324597559439^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143153487 10000000000 1324597559439 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178866081/10000000000 : ℝ)^2151 ≤ (8433264186361/20000000000000 : ℝ)^1639 := by
    have hnat : (5178866081 : ℕ)^2151*20000000000000^1639 ≤ 8433264186361^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178866081 10000000000 8433264186361 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168873709/312500000 : ℝ)^2151 ≤ (5573462932593/12500000000000 : ℝ)^1639 := by
    have hnat : (168873709 : ℕ)^2151*12500000000000^1639 ≤ 5573462932593^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168873709 312500000 5573462932593 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143153487/10000000000 : ℝ), (5178866081/10000000000 : ℝ), (168873709/312500000 : ℝ)] ![(1324597559439/10000000000000 : ℝ), (8433264186361/20000000000000 : ℝ), (5573462932593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143153487/10000000000 : ℝ)|^2151 ≤ (1324597559439/10000000000000 : ℝ)^1639
        have hw : |(-2143153487/10000000000 : ℝ)|=(2143153487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178866081/10000000000 : ℝ)|^2151 ≤ (8433264186361/20000000000000 : ℝ)^1639
        have hw : |(5178866081/10000000000 : ℝ)|=(5178866081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168873709/312500000 : ℝ)|^2151 ≤ (5573462932593/12500000000000 : ℝ)^1639
        have hw : |(168873709/312500000 : ℝ)|=(168873709/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_9 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275312421/10000000000 : ℝ)*x 0 + (-314767/1562500 : ℝ)*x 1 + (2701979413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275312421/10000000000 : ℝ)^2151 ≤ (21599938854833/50000000000000 : ℝ)^1639 := by
    have hnat : (5275312421 : ℕ)^2151*50000000000000^1639 ≤ 21599938854833^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275312421 10000000000 21599938854833 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314767/1562500 : ℝ)^2151 ≤ (6106208660063/50000000000000 : ℝ)^1639 := by
    have hnat : (314767 : ℕ)^2151*50000000000000^1639 ≤ 6106208660063^1639*1562500^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314767 1562500 6106208660063 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701979413/5000000000 : ℝ)^2151 ≤ (5573463119383/12500000000000 : ℝ)^1639 := by
    have hnat : (2701979413 : ℕ)^2151*12500000000000^1639 ≤ 5573463119383^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701979413 5000000000 5573463119383 12500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275312421/10000000000 : ℝ), (-314767/1562500 : ℝ), (2701979413/5000000000 : ℝ)] ![(21599938854833/50000000000000 : ℝ), (6106208660063/50000000000000 : ℝ), (5573463119383/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275312421/10000000000 : ℝ)|^2151 ≤ (21599938854833/50000000000000 : ℝ)^1639
        have hw : |(5275312421/10000000000 : ℝ)|=(5275312421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-314767/1562500 : ℝ)|^2151 ≤ (6106208660063/50000000000000 : ℝ)^1639
        have hw : |(-314767/1562500 : ℝ)|=(314767/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701979413/5000000000 : ℝ)|^2151 ≤ (5573463119383/12500000000000 : ℝ)^1639
        have hw : |(2701979413/5000000000 : ℝ)|=(2701979413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_10 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637655983/5000000000 : ℝ)*x 0 + (1350989781/2500000000 : ℝ)*x 1 + (-201450901/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637655983/5000000000 : ℝ)^2151 ≤ (8639974563937/20000000000000 : ℝ)^1639 := by
    have hnat : (2637655983 : ℕ)^2151*20000000000000^1639 ≤ 8639974563937^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637655983 5000000000 8639974563937 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350989781/2500000000 : ℝ)^2151 ≤ (44587708181929/100000000000000 : ℝ)^1639 := by
    have hnat : (1350989781 : ℕ)^2151*100000000000000^1639 ≤ 44587708181929^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350989781 2500000000 44587708181929 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201450901/1000000000 : ℝ)^2151 ≤ (6106209495441/50000000000000 : ℝ)^1639 := by
    have hnat : (201450901 : ℕ)^2151*50000000000000^1639 ≤ 6106209495441^1639*1000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201450901 1000000000 6106209495441 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637655983/5000000000 : ℝ), (1350989781/2500000000 : ℝ), (-201450901/1000000000 : ℝ)] ![(8639974563937/20000000000000 : ℝ), (44587708181929/100000000000000 : ℝ), (6106209495441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637655983/5000000000 : ℝ)|^2151 ≤ (8639974563937/20000000000000 : ℝ)^1639
        have hw : |(2637655983/5000000000 : ℝ)|=(2637655983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350989781/2500000000 : ℝ)|^2151 ≤ (44587708181929/100000000000000 : ℝ)^1639
        have hw : |(1350989781/2500000000 : ℝ)|=(1350989781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201450901/1000000000 : ℝ)|^2151 ≤ (6106209495441/50000000000000 : ℝ)^1639
        have hw : |(-201450901/1000000000 : ℝ)|=(201450901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_11 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4507590641/10000000000 : ℝ)*x 0 + (2119869783/5000000000 : ℝ)*x 1 + (132491861/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4507590641/10000000000 : ℝ)^2151 ≤ (3514323230647/10000000000000 : ℝ)^1639 := by
    have hnat : (4507590641 : ℕ)^2151*10000000000000^1639 ≤ 3514323230647^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507590641 10000000000 3514323230647 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119869783/5000000000 : ℝ)^2151 ≤ (16214191954863/50000000000000 : ℝ)^1639 := by
    have hnat : (2119869783 : ℕ)^2151*50000000000000^1639 ≤ 16214191954863^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119869783 5000000000 16214191954863 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132491861/312500000 : ℝ)^2151 ≤ (16214191884597/50000000000000 : ℝ)^1639 := by
    have hnat : (132491861 : ℕ)^2151*50000000000000^1639 ≤ 16214191884597^1639*312500000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132491861 312500000 16214191884597 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4507590641/10000000000 : ℝ), (2119869783/5000000000 : ℝ), (132491861/312500000 : ℝ)] ![(3514323230647/10000000000000 : ℝ), (16214191954863/50000000000000 : ℝ), (16214191884597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4507590641/10000000000 : ℝ)|^2151 ≤ (3514323230647/10000000000000 : ℝ)^1639
        have hw : |(4507590641/10000000000 : ℝ)|=(4507590641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119869783/5000000000 : ℝ)|^2151 ≤ (16214191954863/50000000000000 : ℝ)^1639
        have hw : |(2119869783/5000000000 : ℝ)|=(2119869783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132491861/312500000 : ℝ)|^2151 ≤ (16214191884597/50000000000000 : ℝ)^1639
        have hw : |(132491861/312500000 : ℝ)|=(132491861/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_12 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-486970641/2500000000 : ℝ)*x 0 + (5473795711/10000000000 : ℝ)*x 1 + (1313464557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486970641/2500000000 : ℝ)^2151 ≤ (365159354587/3125000000000 : ℝ)^1639 := by
    have hnat : (486970641 : ℕ)^2151*3125000000000^1639 ≤ 365159354587^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486970641 2500000000 365159354587 3125000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473795711/10000000000 : ℝ)^2151 ≤ (22672724539033/50000000000000 : ℝ)^1639 := by
    have hnat : (5473795711 : ℕ)^2151*50000000000000^1639 ≤ 22672724539033^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473795711 10000000000 22672724539033 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313464557/2500000000 : ℝ)^2151 ≤ (21484725782423/50000000000000 : ℝ)^1639 := by
    have hnat : (1313464557 : ℕ)^2151*50000000000000^1639 ≤ 21484725782423^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313464557 2500000000 21484725782423 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-486970641/2500000000 : ℝ), (5473795711/10000000000 : ℝ), (1313464557/2500000000 : ℝ)] ![(365159354587/3125000000000 : ℝ), (22672724539033/50000000000000 : ℝ), (21484725782423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-486970641/2500000000 : ℝ)|^2151 ≤ (365159354587/3125000000000 : ℝ)^1639
        have hw : |(-486970641/2500000000 : ℝ)|=(486970641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473795711/10000000000 : ℝ)|^2151 ≤ (22672724539033/50000000000000 : ℝ)^1639
        have hw : |(5473795711/10000000000 : ℝ)|=(5473795711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313464557/2500000000 : ℝ)|^2151 ≤ (21484725782423/50000000000000 : ℝ)^1639
        have hw : |(1313464557/2500000000 : ℝ)|=(1313464557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_13 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076148653/2000000000 : ℝ)*x 0 + (-2074767651/10000000000 : ℝ)*x 1 + (5253858379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076148653/2000000000 : ℝ)^2151 ≤ (44336486276977/100000000000000 : ℝ)^1639 := by
    have hnat : (1076148653 : ℕ)^2151*100000000000000^1639 ≤ 44336486276977^1639*2000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076148653 2000000000 44336486276977 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2074767651/10000000000 : ℝ)^2151 ≤ (2538812105641/20000000000000 : ℝ)^1639 := by
    have hnat : (2074767651 : ℕ)^2151*20000000000000^1639 ≤ 2538812105641^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074767651 10000000000 2538812105641 20000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253858379/10000000000 : ℝ)^2151 ≤ (4296945318561/10000000000000 : ℝ)^1639 := by
    have hnat : (5253858379 : ℕ)^2151*10000000000000^1639 ≤ 4296945318561^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253858379 10000000000 4296945318561 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076148653/2000000000 : ℝ), (-2074767651/10000000000 : ℝ), (5253858379/10000000000 : ℝ)] ![(44336486276977/100000000000000 : ℝ), (2538812105641/20000000000000 : ℝ), (4296945318561/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076148653/2000000000 : ℝ)|^2151 ≤ (44336486276977/100000000000000 : ℝ)^1639
        have hw : |(1076148653/2000000000 : ℝ)|=(1076148653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2074767651/10000000000 : ℝ)|^2151 ≤ (2538812105641/20000000000000 : ℝ)^1639
        have hw : |(-2074767651/10000000000 : ℝ)|=(2074767651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253858379/10000000000 : ℝ)|^2151 ≤ (4296945318561/10000000000000 : ℝ)^1639
        have hw : |(5253858379/10000000000 : ℝ)|=(5253858379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_14 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2690371847/5000000000 : ℝ)*x 0 + (5253858113/10000000000 : ℝ)*x 1 + (-518691857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690371847/5000000000 : ℝ)^2151 ≤ (1108412272903/2500000000000 : ℝ)^1639 := by
    have hnat : (2690371847 : ℕ)^2151*2500000000000^1639 ≤ 1108412272903^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690371847 5000000000 1108412272903 2500000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253858113/10000000000 : ℝ)^2151 ≤ (42969450330489/100000000000000 : ℝ)^1639 := by
    have hnat : (5253858113 : ℕ)^2151*100000000000000^1639 ≤ 42969450330489^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253858113 10000000000 42969450330489 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518691857/2500000000 : ℝ)^2151 ≤ (1269405873761/10000000000000 : ℝ)^1639 := by
    have hnat : (518691857 : ℕ)^2151*10000000000000^1639 ≤ 1269405873761^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518691857 2500000000 1269405873761 10000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690371847/5000000000 : ℝ), (5253858113/10000000000 : ℝ), (-518691857/2500000000 : ℝ)] ![(1108412272903/2500000000000 : ℝ), (42969450330489/100000000000000 : ℝ), (1269405873761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690371847/5000000000 : ℝ)|^2151 ≤ (1108412272903/2500000000000 : ℝ)^1639
        have hw : |(2690371847/5000000000 : ℝ)|=(2690371847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253858113/10000000000 : ℝ)|^2151 ≤ (42969450330489/100000000000000 : ℝ)^1639
        have hw : |(5253858113/10000000000 : ℝ)|=(5253858113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518691857/2500000000 : ℝ)|^2151 ≤ (1269405873761/10000000000000 : ℝ)^1639
        have hw : |(-518691857/2500000000 : ℝ)|=(518691857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1342_box_15 (p : ℝ) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1037684417/2500000000 : ℝ)*x 0 + (2209080279/5000000000 : ℝ)*x 1 + (4418160761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037684417/2500000000 : ℝ)^2151 ≤ (31537925601179/100000000000000 : ℝ)^1639 := by
    have hnat : (1037684417 : ℕ)^2151*100000000000000^1639 ≤ 31537925601179^1639*2500000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037684417 2500000000 31537925601179 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209080279/5000000000 : ℝ)^2151 ≤ (17115518080609/50000000000000 : ℝ)^1639 := by
    have hnat : (2209080279 : ℕ)^2151*50000000000000^1639 ≤ 17115518080609^1639*5000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209080279 5000000000 17115518080609 50000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4418160761/10000000000 : ℝ)^2151 ≤ (34231038225343/100000000000000 : ℝ)^1639 := by
    have hnat : (4418160761 : ℕ)^2151*100000000000000^1639 ≤ 34231038225343^1639*10000000000^2151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4418160761 10000000000 34231038225343 100000000000000 2151 1639 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2151/512 : ℝ)) 2151 1639 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037684417/2500000000 : ℝ), (2209080279/5000000000 : ℝ), (4418160761/10000000000 : ℝ)] ![(31537925601179/100000000000000 : ℝ), (17115518080609/50000000000000 : ℝ), (34231038225343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037684417/2500000000 : ℝ)|^2151 ≤ (31537925601179/100000000000000 : ℝ)^1639
        have hw : |(1037684417/2500000000 : ℝ)|=(1037684417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209080279/5000000000 : ℝ)|^2151 ≤ (17115518080609/50000000000000 : ℝ)^1639
        have hw : |(2209080279/5000000000 : ℝ)|=(2209080279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4418160761/10000000000 : ℝ)|^2151 ≤ (34231038225343/100000000000000 : ℝ)^1639
        have hw : |(4418160761/10000000000 : ℝ)|=(4418160761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1342_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12571/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58941/100000 : ℝ) ∧ (39977/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2636/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/2000 : ℝ) ^ (4301/1024 : ℝ) ≤ (2490625169075167/25000000000000000000 : ℝ) := by
    have hpowers : (223/2000 : ℝ)^4301 ≤ (2490625169075167/25000000000000000000 : ℝ)^1024 := by
      have hnat : (223 : ℕ)^4301*25000000000000000000^1024 ≤ 2490625169075167^1024*2000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 2000 2490625169075167 25000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/2000 : ℝ)) (X := (2490625169075167/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7353/50000 : ℝ) ^ (4301/1024 : ℝ) ≤ (31865046762550107/100000000000000000000 : ℝ) := by
    have hpowers : (7353/50000 : ℝ)^4301 ≤ (31865046762550107/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7353 : ℕ)^4301*100000000000000000000^1024 ≤ 31865046762550107^1024*50000^4301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7353 50000 31865046762550107 100000000000000000000 4301 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7353/50000 : ℝ)) (X := (31865046762550107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502490625169075167/12500000000000000000 : ℝ) ≤ (125005929334121/125000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (12502490625169075167/12500000000000000000 : ℝ)^1024 ≤ (125005929334121/125000000000000 : ℝ)^4301 := by
      have hnat : (12502490625169075167 : ℕ)^1024*125000000000000^4301 ≤ 125005929334121^4301*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502490625169075167 12500000000000000000 125005929334121 125000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125005929334121/125000000000000 : ℝ)) (X := (12502490625169075167/12500000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001673101897554031/4000000000000000000 : ℝ) ≤ (10000995689032029/10000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (4001673101897554031/4000000000000000000 : ℝ)^1024 ≤ (10000995689032029/10000000000000000 : ℝ)^4301 := by
      have hnat : (4001673101897554031 : ℕ)^1024*10000000000000000^4301 ≤ 10000995689032029^4301*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001673101897554031 4000000000000000000 10000995689032029 10000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000995689032029/10000000000000000 : ℝ)) (X := (4001673101897554031/4000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031865046762550107/50000000000000000000 : ℝ) ≤ (5000758515667189/5000000000000000 : ℝ) ^ (4301/1024 : ℝ) := by
    have hpowers : (50031865046762550107/50000000000000000000 : ℝ)^1024 ≤ (5000758515667189/5000000000000000 : ℝ)^4301 := by
      have hnat : (50031865046762550107 : ℕ)^1024*5000000000000000^4301 ≤ 5000758515667189^4301*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031865046762550107 50000000000000000000 5000758515667189 5000000000000000 1024 4301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000758515667189/5000000000000000 : ℝ)) (X := (50031865046762550107/50000000000000000000 : ℝ)) (by norm_num) 4301 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2490625169075167/25000000000000000000 : ℝ) ≤ ((1777503042181417969/1778000000000000000 : ℝ)+2*(521342302349/355600000000000 : ℝ)*(223/2000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (1777503042181417969/1778000000000000000 : ℝ)+2*(521342302349/355600000000000 : ℝ)*(223/2000 : ℝ)=(125005929334121/125000000000000 : ℝ) by norm_num, show 1+2*(2490625169075167/25000000000000000000 : ℝ)=(12502490625169075167/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31865046762550107/100000000000000000000 : ℝ)+(2490625169075167/25000000000000000000 : ℝ) ≤ ((1777503042181417969/1778000000000000000 : ℝ)+(521342302349/355600000000000 : ℝ)*((7353/50000 : ℝ)+(223/2000 : ℝ)))^(4301/1024 : ℝ) := by
    rw [show (1777503042181417969/1778000000000000000 : ℝ)+(521342302349/355600000000000 : ℝ)*((7353/50000 : ℝ)+(223/2000 : ℝ))=(10000995689032029/10000000000000000 : ℝ) by norm_num, show 1+(31865046762550107/100000000000000000000 : ℝ)+(2490625169075167/25000000000000000000 : ℝ)=(4001673101897554031/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31865046762550107/100000000000000000000 : ℝ) ≤ ((1777503042181417969/1778000000000000000 : ℝ)+2*(521342302349/355600000000000 : ℝ)*(7353/50000 : ℝ))^(4301/1024 : ℝ) := by
    rw [show (1777503042181417969/1778000000000000000 : ℝ)+2*(521342302349/355600000000000 : ℝ)*(7353/50000 : ℝ)=(5000758515667189/5000000000000000 : ℝ) by norm_num, show 1+2*(31865046762550107/100000000000000000000 : ℝ)=(50031865046762550107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1777503042181417969/1778000000000000000 : ℝ)*(X 1 0+X 2 0)+(521342302349/355600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (223/2000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (1777503042181417969/1778000000000000000 : ℝ)) (alpha := (521342302349/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1777503042181417969/1778000000000000000 : ℝ)*(X 0 1+X 2 1)+(521342302349/355600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (223/2000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (1777503042181417969/1778000000000000000 : ℝ)) (alpha := (521342302349/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1777503042181417969/1778000000000000000 : ℝ)*(X 0 2+X 1 2)+(521342302349/355600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4301/1024 : ℝ)) (lo := (223/2000 : ℝ)) (hi := (7353/50000 : ℝ)) (c := (1777503042181417969/1778000000000000000 : ℝ)) (alpha := (521342302349/355600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-58647567/312500000 : ℝ)*X 0 0+(2694969613/5000000000 : ℝ)*X 0 1+(673742377/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330322831/625000000 : ℝ)*X 1 0+(-126266637/625000000 : ℝ)*X 1 1+(84217801/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642582539/5000000000 : ℝ)*X 2 0+(5389939371/10000000000 : ℝ)*X 2 1+(-2020266341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4474808611/10000000000 : ℝ)*X 0 0+(2128208937/5000000000 : ℝ)*X 0 1+(4256418169/10000000000 : ℝ)*X 0 2+(4474808611/10000000000 : ℝ)*X 1 0+(2128208937/5000000000 : ℝ)*X 1 1+(4256418169/10000000000 : ℝ)*X 1 2+(4474808611/10000000000 : ℝ)*X 2 0+(2128208937/5000000000 : ℝ)*X 2 1+(4256418169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106988287/5000000000 : ℝ)*X 0 0+(164529007/312500000 : ℝ)*X 0 1+(5264927303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686485873/5000000000 : ℝ)*X 1 0+(-414085861/2000000000 : ℝ)*X 1 1+(2632463511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686485537/5000000000 : ℝ)*X 2 0+(2632463667/5000000000 : ℝ)*X 2 1+(-64700931/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1044377389/2500000000 : ℝ)*X 0 0+(2202506777/5000000000 : ℝ)*X 0 1+(88100287/200000000 : ℝ)*X 0 2+(1044377389/2500000000 : ℝ)*X 1 0+(2202506777/5000000000 : ℝ)*X 1 1+(88100287/200000000 : ℝ)*X 1 2+(1044377389/2500000000 : ℝ)*X 2 0+(2202506777/5000000000 : ℝ)*X 2 1+(88100287/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2143153487/10000000000 : ℝ)*X 0 0+(5178866081/10000000000 : ℝ)*X 0 1+(168873709/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275312421/10000000000 : ℝ)*X 1 0+(-314767/1562500 : ℝ)*X 1 1+(2701979413/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637655983/5000000000 : ℝ)*X 2 0+(1350989781/2500000000 : ℝ)*X 2 1+(-201450901/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4507590641/10000000000 : ℝ)*X 0 0+(2119869783/5000000000 : ℝ)*X 0 1+(132491861/312500000 : ℝ)*X 0 2+(4507590641/10000000000 : ℝ)*X 1 0+(2119869783/5000000000 : ℝ)*X 1 1+(132491861/312500000 : ℝ)*X 1 2+(4507590641/10000000000 : ℝ)*X 2 0+(2119869783/5000000000 : ℝ)*X 2 1+(132491861/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-486970641/2500000000 : ℝ)*X 0 0+(5473795711/10000000000 : ℝ)*X 0 1+(1313464557/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1076148653/2000000000 : ℝ)*X 1 0+(-2074767651/10000000000 : ℝ)*X 1 1+(5253858379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690371847/5000000000 : ℝ)*X 2 0+(5253858113/10000000000 : ℝ)*X 2 1+(-518691857/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1037684417/2500000000 : ℝ)*X 0 0+(2209080279/5000000000 : ℝ)*X 0 1+(4418160761/10000000000 : ℝ)*X 0 2+(1037684417/2500000000 : ℝ)*X 1 0+(2209080279/5000000000 : ℝ)*X 1 1+(4418160761/10000000000 : ℝ)*X 1 2+(1037684417/2500000000 : ℝ)*X 2 0+(2209080279/5000000000 : ℝ)*X 2 1+(4418160761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1342_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12571/20000 : ℝ) ≤ (-319292045906056255686022739211/508000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1749951/25000000000000 : ℝ)*(upper3) + (155754363/50000000000000 : ℝ)*(lower4) + (10942961/100000000000000 : ℝ)*(lower5) + (116827615678837/4000000000000 : ℝ)*(major0) + (116827615678837/4000000000000 : ℝ)*(major1) + (116827615678837/4000000000000 : ℝ)*(major2) + (3488701873/20000000000000 : ℝ)*(sp1) + (22501134173/100000000000000 : ℝ)*(sp2) + (8050948273/100000000000000 : ℝ)*(sp3) + (248418954230259/6250000000000 : ℝ)*(sp4) + (496836621489663/12500000000000 : ℝ)*(sp5) + (248417994643281/6250000000000 : ℝ)*(sp6) + (1887613239214279/100000000000000 : ℝ)*(sp7) + (285909701/4000000000000 : ℝ)*(sp8) + (235952661270319/12500000000000 : ℝ)*(f.failure) + (397471041542667/10000000000000 : ℝ)*(f.sum) + (1879467204973/508000000000000000000000000 : ℝ)*base66 + (2459243948585579/1016000000000000000000000000000 : ℝ)*base67 + (6734955315865579/1016000000000000000000000000000 : ℝ)*base69 + (5828935149753579/1016000000000000000000000000000 : ℝ)*base71 + (80098577149/508000000000000000000000000 : ℝ)*base74 + (2206028416409579/1016000000000000000000000000000 : ℝ)*base75 + (9358741273769579/1016000000000000000000000000000 : ℝ)*base77 + (5140431305529579/1016000000000000000000000000000 : ℝ)*base79 + (725348286901/508000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4600099/1250000000000000000000 : ℝ)*base89 + (4600099/1250000000000000000000 : ℝ)*base91 + (4600099/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58941/100000 : ℝ) ≤ (6550119550861539096995935639593/11112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14654941/100000000000000 : ℝ)*(lower1) + (49268041/50000000000000 : ℝ)*(upper2) + (2399/31250000000 : ℝ)*(upper3) + (3848933/100000000000000 : ℝ)*(lower5) + (2989376386847997/100000000000000 : ℝ)*(major0) + (2989376386847997/100000000000000 : ℝ)*(major1) + (1494688193423999/50000000000000 : ℝ)*(major2) + (1006773078531227/25000000000000 : ℝ)*(sp0) + (4027086111520633/100000000000000 : ℝ)*(sp1) + (503385916907823/12500000000000 : ℝ)*(sp2) + (1932012302076473/100000000000000 : ℝ)*(sp3) + (248104171/4000000000000 : ℝ)*(sp5) + (1244715581/25000000000000 : ℝ)*(sp6) + (254829853/100000000000000 : ℝ)*(sp7) + (966006278453163/50000000000000 : ℝ)*(f.failure) + (1006773078531227/25000000000000 : ℝ)*(f.sum) + (24179805764677/7112000000000000000000000000 : ℝ)*base66 + (2403212984517631907/177800000000000000000000000000000 : ℝ)*base68 + (363505991766679469/88900000000000000000000000000000 : ℝ)*base70 + (928593767620231907/177800000000000000000000000000000 : ℝ)*base72 + (263465799697/1422400000000000000000000000 : ℝ)*base74 + (1896714741929279469/88900000000000000000000000000000 : ℝ)*base76 + (99599471529996701/25400000000000000000000000000000 : ℝ)*base78 + (203539396872996701/25400000000000000000000000000000 : ℝ)*base80 + (360361241103347/17780000000000000000000000000 : ℝ)*base82 + (74078223/5000000000000000000000 : ℝ)*base89 + (74078223/5000000000000000000000 : ℝ)*base91 + (24078223/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39977/50000 : ℝ) ≤ (17770423686366235913326189280289/22225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120388657/25000000000000 : ℝ)*(upper0) + (290385791/50000000000000 : ℝ)*(upper1) + (6159121/3125000000000 : ℝ)*(upper2) + (1650756715836427/50000000000000 : ℝ)*(major0) + (1650756715836427/50000000000000 : ℝ)*(major1) + (660302686334571/20000000000000 : ℝ)*(major2) + (609689391971/100000000000000 : ℝ)*(sp1) + (122959554783/20000000000000 : ℝ)*(sp2) + (92692385441/100000000000000 : ℝ)*(sp3) + (956069853/6250000000000 : ℝ)*(sp4) + (2221307383975023/50000000000000 : ℝ)*(sp8) + (4442020375675723/100000000000000 : ℝ)*(sp9) + (222100763364689/5000000000000 : ℝ)*(sp10) + (1066825900950507/50000000000000 : ℝ)*(sp11) + (1066872247143227/50000000000000 : ℝ)*(f.failure) + (2221315032533847/50000000000000 : ℝ)*(f.sum) + (111821896994319/35560000000000000000000000000 : ℝ)*base66 + (527387660266855737/88900000000000000000000000000000 : ℝ)*base68 + (326962557755087701/35560000000000000000000000000000 : ℝ)*base70 + (1351806876500055737/88900000000000000000000000000000 : ℝ)*base72 + (287905467534119/35560000000000000000000000000 : ℝ)*base74 + (6981844966912299/35560000000000000000000000000000 : ℝ)*base75 + (212204370998546891/12700000000000000000000000000000 : ℝ)*base78 + (61548008202146891/12700000000000000000000000000000 : ℝ)*base80 + (28570370237643/8890000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3199967/5000000000000000000000 : ℝ)*base89 + (3199967/5000000000000000000000 : ℝ)*base91 + (46800033/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-2636/3125 : ℝ) ≤ (-74986721833649588121787328601057/88900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69108141/100000000000000 : ℝ)*(lower1) + (18762017/12500000000000 : ℝ)*(lower2) + (101155371/100000000000000 : ℝ)*(upper5) + (3337970334587549/100000000000000 : ℝ)*(major0) + (3337970334587549/100000000000000 : ℝ)*(major1) + (66759406691751/2000000000000 : ℝ)*(major2) + (2076219311/25000000000000 : ℝ)*(sp0) + (2050217479/2000000000000 : ℝ)*(sp5) + (32067950311/20000000000000 : ℝ)*(sp6) + (7301434781/50000000000000 : ℝ)*(sp7) + (2273371270394377/50000000000000 : ℝ)*(sp12) + (4546648334792047/100000000000000 : ℝ)*(sp13) + (4546590505914443/100000000000000 : ℝ)*(sp14) + (2157291726763887/100000000000000 : ℝ)*(sp15) + (2157306329633449/100000000000000 : ℝ)*(f.failure) + (2273375422832999/50000000000000 : ℝ)*(f.sum) + (1642945980887/5080000000000000000000000000 : ℝ)*base66 + (1052957375422582019/177800000000000000000000000000000 : ℝ)*base68 + (9638729731054181/3556000000000000000000000000000 : ℝ)*base70 + (125155983941617981/177800000000000000000000000000000 : ℝ)*base71 + (12861020323967/5080000000000000000000000000 : ℝ)*base74 + (25190622871213819/3556000000000000000000000000000 : ℝ)*base75 + (59939144949246717/25400000000000000000000000000000 : ℝ)*base78 + (170488078613446717/25400000000000000000000000000000 : ℝ)*base80 + (37175942941939/17780000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (99243829/10000000000000000000000 : ℝ)*base89 + (99243829/10000000000000000000000 : ℝ)*base91 + (756171/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1342_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58941/100000 : ℝ) else (39977/50000 : ℝ) ≤ X j i ∧ X j i ≤ (2636/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1342_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1342_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58941/100000 : ℝ) else (39977/50000 : ℝ) ≤ X j i ∧ X j i ≤ (2636/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1342_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1342_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1342_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4301/1024 : ℝ) ≤ p) (hpb : p ≤ (2151/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154728621/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2943/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12571/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58941/100000 : ℝ) else (39977/50000 : ℝ) ≤ X j i ∧ X j i ≤ (2636/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1342_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
