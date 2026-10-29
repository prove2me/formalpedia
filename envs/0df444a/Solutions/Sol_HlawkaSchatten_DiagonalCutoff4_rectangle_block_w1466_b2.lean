-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1466_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:09:25.147998+00:00
-- url     : https://prove2.me/submissions/f197700f-0239-45cb-9715-4c71cb892604

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
theorem support_rectangle_w1466_s6_0 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-121135989/625000000 : ℝ)*x 0 + (543928771/1000000000 : ℝ)*x 1 + (5214950957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121135989/625000000 : ℝ)^4429 ≤ (5916405359711/50000000000000 : ℝ)^3405 := by
    have hnat : (121135989 : ℕ)^4429*50000000000000^3405 ≤ 5916405359711^3405*625000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121135989 625000000 5916405359711 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543928771/1000000000 : ℝ)^4429 ≤ (11322712512411/25000000000000 : ℝ)^3405 := by
    have hnat : (543928771 : ℕ)^4429*25000000000000^3405 ≤ 11322712512411^3405*1000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543928771 1000000000 11322712512411 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214950957/10000000000 : ℝ)^4429 ≤ (1071908480331/2500000000000 : ℝ)^3405 := by
    have hnat : (5214950957 : ℕ)^4429*2500000000000^3405 ≤ 1071908480331^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214950957 10000000000 1071908480331 2500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121135989/625000000 : ℝ), (543928771/1000000000 : ℝ), (5214950957/10000000000 : ℝ)] ![(5916405359711/50000000000000 : ℝ), (11322712512411/25000000000000 : ℝ), (1071908480331/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121135989/625000000 : ℝ)|^4429 ≤ (5916405359711/50000000000000 : ℝ)^3405
        have hw : |(-121135989/625000000 : ℝ)|=(121135989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543928771/1000000000 : ℝ)|^4429 ≤ (11322712512411/25000000000000 : ℝ)^3405
        have hw : |(543928771/1000000000 : ℝ)|=(543928771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214950957/10000000000 : ℝ)|^4429 ≤ (1071908480331/2500000000000 : ℝ)^3405
        have hw : |(5214950957/10000000000 : ℝ)|=(5214950957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_1 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677009893/5000000000 : ℝ)*x 0 + (-2053182973/10000000000 : ℝ)*x 1 + (2607475467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677009893/5000000000 : ℝ)^4429 ≤ (8873904527961/20000000000000 : ℝ)^3405 := by
    have hnat : (2677009893 : ℕ)^4429*20000000000000^3405 ≤ 8873904527961^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677009893 5000000000 8873904527961 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2053182973/10000000000 : ℝ)^4429 ≤ (12754138380323/100000000000000 : ℝ)^3405 := by
    have hnat : (2053182973 : ℕ)^4429*100000000000000^3405 ≤ 12754138380323^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053182973 10000000000 12754138380323 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607475467/5000000000 : ℝ)^4429 ≤ (42876338967269/100000000000000 : ℝ)^3405 := by
    have hnat : (2607475467 : ℕ)^4429*100000000000000^3405 ≤ 42876338967269^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607475467 5000000000 42876338967269 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677009893/5000000000 : ℝ), (-2053182973/10000000000 : ℝ), (2607475467/5000000000 : ℝ)] ![(8873904527961/20000000000000 : ℝ), (12754138380323/100000000000000 : ℝ), (42876338967269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677009893/5000000000 : ℝ)|^4429 ≤ (8873904527961/20000000000000 : ℝ)^3405
        have hw : |(2677009893/5000000000 : ℝ)|=(2677009893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2053182973/10000000000 : ℝ)|^4429 ≤ (12754138380323/100000000000000 : ℝ)^3405
        have hw : |(-2053182973/10000000000 : ℝ)|=(2053182973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607475467/5000000000 : ℝ)|^4429 ≤ (42876338967269/100000000000000 : ℝ)^3405
        have hw : |(2607475467/5000000000 : ℝ)|=(2607475467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_2 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354019753/10000000000 : ℝ)*x 0 + (1042990199/2000000000 : ℝ)*x 1 + (-256647867/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354019753/10000000000 : ℝ)^4429 ≤ (22184761142043/50000000000000 : ℝ)^3405 := by
    have hnat : (5354019753 : ℕ)^4429*50000000000000^3405 ≤ 22184761142043^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354019753 10000000000 22184761142043 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042990199/2000000000 : ℝ)^4429 ≤ (21438169809813/50000000000000 : ℝ)^3405 := by
    have hnat : (1042990199 : ℕ)^4429*50000000000000^3405 ≤ 21438169809813^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042990199 2000000000 21438169809813 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256647867/1250000000 : ℝ)^4429 ≤ (6377069040681/50000000000000 : ℝ)^3405 := by
    have hnat : (256647867 : ℕ)^4429*50000000000000^3405 ≤ 6377069040681^3405*1250000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256647867 1250000000 6377069040681 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354019753/10000000000 : ℝ), (1042990199/2000000000 : ℝ), (-256647867/1250000000 : ℝ)] ![(22184761142043/50000000000000 : ℝ), (21438169809813/50000000000000 : ℝ), (6377069040681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354019753/10000000000 : ℝ)|^4429 ≤ (22184761142043/50000000000000 : ℝ)^3405
        have hw : |(5354019753/10000000000 : ℝ)|=(5354019753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042990199/2000000000 : ℝ)|^4429 ≤ (21438169809813/50000000000000 : ℝ)^3405
        have hw : |(1042990199/2000000000 : ℝ)|=(1042990199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256647867/1250000000 : ℝ)|^4429 ≤ (6377069040681/50000000000000 : ℝ)^3405
        have hw : |(-256647867/1250000000 : ℝ)|=(256647867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_3 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291685419/10000000000 : ℝ)*x 0 + (4051785321/10000000000 : ℝ)*x 1 + (181761741/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291685419/10000000000 : ℝ)^4429 ≤ (33277179927551/100000000000000 : ℝ)^3405 := by
    have hnat : (4291685419 : ℕ)^4429*100000000000000^3405 ≤ 33277179927551^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291685419 10000000000 33277179927551 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4051785321/10000000000 : ℝ)^4429 ≤ (1929888865419/6250000000000 : ℝ)^3405 := by
    have hnat : (4051785321 : ℕ)^4429*6250000000000^3405 ≤ 1929888865419^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051785321 10000000000 1929888865419 6250000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181761741/400000000 : ℝ)^4429 ≤ (7168919643249/20000000000000 : ℝ)^3405 := by
    have hnat : (181761741 : ℕ)^4429*20000000000000^3405 ≤ 7168919643249^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181761741 400000000 7168919643249 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291685419/10000000000 : ℝ), (4051785321/10000000000 : ℝ), (181761741/400000000 : ℝ)] ![(33277179927551/100000000000000 : ℝ), (1929888865419/6250000000000 : ℝ), (7168919643249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291685419/10000000000 : ℝ)|^4429 ≤ (33277179927551/100000000000000 : ℝ)^3405
        have hw : |(4291685419/10000000000 : ℝ)|=(4291685419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4051785321/10000000000 : ℝ)|^4429 ≤ (1929888865419/6250000000000 : ℝ)^3405
        have hw : |(4051785321/10000000000 : ℝ)|=(4051785321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181761741/400000000 : ℝ)|^4429 ≤ (7168919643249/20000000000000 : ℝ)^3405
        have hw : |(181761741/400000000 : ℝ)|=(181761741/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_4 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1938206849/10000000000 : ℝ)*x 0 + (5216095597/10000000000 : ℝ)*x 1 + (1087626931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1938206849/10000000000 : ℝ)^4429 ≤ (5916528547071/50000000000000 : ℝ)^3405 := by
    have hnat : (1938206849 : ℕ)^4429*50000000000000^3405 ≤ 5916528547071^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938206849 10000000000 5916528547071 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216095597/10000000000 : ℝ)^4429 ≤ (171554323377/400000000000 : ℝ)^3405 := by
    have hnat : (5216095597 : ℕ)^4429*400000000000^3405 ≤ 171554323377^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216095597 10000000000 171554323377 400000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087626931/2000000000 : ℝ)^4429 ≤ (11319590510301/25000000000000 : ℝ)^3405 := by
    have hnat : (1087626931 : ℕ)^4429*25000000000000^3405 ≤ 11319590510301^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087626931 2000000000 11319590510301 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1938206849/10000000000 : ℝ), (5216095597/10000000000 : ℝ), (1087626931/2000000000 : ℝ)] ![(5916528547071/50000000000000 : ℝ), (171554323377/400000000000 : ℝ), (11319590510301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1938206849/10000000000 : ℝ)|^4429 ≤ (5916528547071/50000000000000 : ℝ)^3405
        have hw : |(-1938206849/10000000000 : ℝ)|=(1938206849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216095597/10000000000 : ℝ)|^4429 ≤ (171554323377/400000000000 : ℝ)^3405
        have hw : |(5216095597/10000000000 : ℝ)|=(5216095597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087626931/2000000000 : ℝ)|^4429 ≤ (11319590510301/25000000000000 : ℝ)^3405
        have hw : |(1087626931/2000000000 : ℝ)|=(1087626931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_5 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295575579/10000000000 : ℝ)*x 0 + (-914999617/5000000000 : ℝ)*x 1 + (2719067339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295575579/10000000000 : ℝ)^4429 ≤ (43740567664297/100000000000000 : ℝ)^3405 := by
    have hnat : (5295575579 : ℕ)^4429*100000000000000^3405 ≤ 43740567664297^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295575579 10000000000 43740567664297 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914999617/5000000000 : ℝ)^4429 ≤ (10981070029329/100000000000000 : ℝ)^3405 := by
    have hnat : (914999617 : ℕ)^4429*100000000000000^3405 ≤ 10981070029329^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914999617 5000000000 10981070029329 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719067339/5000000000 : ℝ)^4429 ≤ (9055672458059/20000000000000 : ℝ)^3405 := by
    have hnat : (2719067339 : ℕ)^4429*20000000000000^3405 ≤ 9055672458059^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719067339 5000000000 9055672458059 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295575579/10000000000 : ℝ), (-914999617/5000000000 : ℝ), (2719067339/5000000000 : ℝ)] ![(43740567664297/100000000000000 : ℝ), (10981070029329/100000000000000 : ℝ), (9055672458059/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295575579/10000000000 : ℝ)|^4429 ≤ (43740567664297/100000000000000 : ℝ)^3405
        have hw : |(5295575579/10000000000 : ℝ)|=(5295575579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914999617/5000000000 : ℝ)|^4429 ≤ (10981070029329/100000000000000 : ℝ)^3405
        have hw : |(-914999617/5000000000 : ℝ)|=(914999617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719067339/5000000000 : ℝ)|^4429 ≤ (9055672458059/20000000000000 : ℝ)^3405
        have hw : |(2719067339/5000000000 : ℝ)|=(2719067339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_6 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647787797/5000000000 : ℝ)*x 0 + (1359533673/2500000000 : ℝ)*x 1 + (-1829999193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647787797/5000000000 : ℝ)^4429 ≤ (21870283912727/50000000000000 : ℝ)^3405 := by
    have hnat : (2647787797 : ℕ)^4429*50000000000000^3405 ≤ 21870283912727^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647787797 5000000000 21870283912727 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359533673/2500000000 : ℝ)^4429 ≤ (9055672488383/20000000000000 : ℝ)^3405 := by
    have hnat : (1359533673 : ℕ)^4429*20000000000000^3405 ≤ 9055672488383^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359533673 2500000000 9055672488383 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1829999193/10000000000 : ℝ)^4429 ≤ (10981069709317/100000000000000 : ℝ)^3405 := by
    have hnat : (1829999193 : ℕ)^4429*100000000000000^3405 ≤ 10981069709317^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829999193 10000000000 10981069709317 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647787797/5000000000 : ℝ), (1359533673/2500000000 : ℝ), (-1829999193/10000000000 : ℝ)] ![(21870283912727/50000000000000 : ℝ), (9055672488383/20000000000000 : ℝ), (10981069709317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647787797/5000000000 : ℝ)|^4429 ≤ (21870283912727/50000000000000 : ℝ)^3405
        have hw : |(2647787797/5000000000 : ℝ)|=(2647787797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359533673/2500000000 : ℝ)|^4429 ≤ (9055672488383/20000000000000 : ℝ)^3405
        have hw : |(1359533673/2500000000 : ℝ)|=(1359533673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1829999193/10000000000 : ℝ)|^4429 ≤ (10981069709317/100000000000000 : ℝ)^3405
        have hw : |(-1829999193/10000000000 : ℝ)|=(1829999193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s6_7 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291753491/10000000000 : ℝ)*x 0 + (90830637/200000000 : ℝ)*x 1 + (20271577/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291753491/10000000000 : ℝ)^4429 ≤ (33277866484781/100000000000000 : ℝ)^3405 := by
    have hnat : (4291753491 : ℕ)^4429*100000000000000^3405 ≤ 33277866484781^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291753491 10000000000 33277866484781 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90830637/200000000 : ℝ)^4429 ≤ (8954707310389/25000000000000 : ℝ)^3405 := by
    have hnat : (90830637 : ℕ)^4429*25000000000000^3405 ≤ 8954707310389^3405*200000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90830637 200000000 8954707310389 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20271577/50000000 : ℝ)^4429 ≤ (3090330425727/10000000000000 : ℝ)^3405 := by
    have hnat : (20271577 : ℕ)^4429*10000000000000^3405 ≤ 3090330425727^3405*50000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20271577 50000000 3090330425727 10000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291753491/10000000000 : ℝ), (90830637/200000000 : ℝ), (20271577/50000000 : ℝ)] ![(33277866484781/100000000000000 : ℝ), (8954707310389/25000000000000 : ℝ), (3090330425727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291753491/10000000000 : ℝ)|^4429 ≤ (33277866484781/100000000000000 : ℝ)^3405
        have hw : |(4291753491/10000000000 : ℝ)|=(4291753491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90830637/200000000 : ℝ)|^4429 ≤ (8954707310389/25000000000000 : ℝ)^3405
        have hw : |(90830637/200000000 : ℝ)|=(90830637/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20271577/50000000 : ℝ)|^4429 ≤ (3090330425727/10000000000000 : ℝ)^3405
        have hw : |(20271577/50000000 : ℝ)|=(20271577/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1466_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (429/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (967/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10723/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10723/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10723/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10723/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10723/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10723/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10723/100000 : ℝ) ^ (4427/1024 : ℝ) ≤ (3212125830804867/50000000000000000000 : ℝ) := by
    have hpowers : (10723/100000 : ℝ)^4427 ≤ (3212125830804867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10723 : ℕ)^4427*50000000000000000000^1024 ≤ 3212125830804867^1024*100000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10723 100000 3212125830804867 50000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10723/100000 : ℝ)) (X := (3212125830804867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4427/1024 : ℝ) ≤ (15682877265908823/50000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4427 ≤ (15682877265908823/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4427*50000000000000000000^1024 ≤ 15682877265908823^1024*50000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 15682877265908823 50000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (15682877265908823/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003212125830804867/25000000000000000000 : ℝ) ≤ (2500074295333919/2500000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (25003212125830804867/25000000000000000000 : ℝ)^1024 ≤ (2500074295333919/2500000000000000 : ℝ)^4427 := by
      have hnat : (25003212125830804867 : ℕ)^1024*2500000000000000^4427 ≤ 2500074295333919^4427*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003212125830804867 25000000000000000000 2500074295333919 2500000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074295333919/2500000000000000 : ℝ)) (X := (25003212125830804867/25000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001889500309671369/5000000000000000000 : ℝ) ≤ (10000873985703103/10000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (5001889500309671369/5000000000000000000 : ℝ)^1024 ≤ (10000873985703103/10000000000000000 : ℝ)^4427 := by
      have hnat : (5001889500309671369 : ℕ)^1024*10000000000000000^4427 ≤ 10000873985703103^4427*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001889500309671369 5000000000000000000 10000873985703103 10000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000873985703103/10000000000000000 : ℝ)) (X := (5001889500309671369/5000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015682877265908823/25000000000000000000 : ℝ) ≤ (1000145079007053/1000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (25015682877265908823/25000000000000000000 : ℝ)^1024 ≤ (1000145079007053/1000000000000000 : ℝ)^4427 := by
      have hnat : (25015682877265908823 : ℕ)^1024*1000000000000000^4427 ≤ 1000145079007053^4427*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015682877265908823 25000000000000000000 1000145079007053 1000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000145079007053/1000000000000000 : ℝ)) (X := (25015682877265908823/25000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3212125830804867/50000000000000000000 : ℝ) ≤ ((23749520881030978617/23755000000000000000 : ℝ)+2*(576804367427/475100000000000 : ℝ)*(10723/100000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (23749520881030978617/23755000000000000000 : ℝ)+2*(576804367427/475100000000000 : ℝ)*(10723/100000 : ℝ)=(2500074295333919/2500000000000000 : ℝ) by norm_num, show 1+2*(3212125830804867/50000000000000000000 : ℝ)=(25003212125830804867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15682877265908823/50000000000000000000 : ℝ)+(3212125830804867/50000000000000000000 : ℝ) ≤ ((23749520881030978617/23755000000000000000 : ℝ)+(576804367427/475100000000000 : ℝ)*((7737/50000 : ℝ)+(10723/100000 : ℝ)))^(4427/1024 : ℝ) := by
    rw [show (23749520881030978617/23755000000000000000 : ℝ)+(576804367427/475100000000000 : ℝ)*((7737/50000 : ℝ)+(10723/100000 : ℝ))=(10000873985703103/10000000000000000 : ℝ) by norm_num, show 1+(15682877265908823/50000000000000000000 : ℝ)+(3212125830804867/50000000000000000000 : ℝ)=(5001889500309671369/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15682877265908823/50000000000000000000 : ℝ) ≤ ((23749520881030978617/23755000000000000000 : ℝ)+2*(576804367427/475100000000000 : ℝ)*(7737/50000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (23749520881030978617/23755000000000000000 : ℝ)+2*(576804367427/475100000000000 : ℝ)*(7737/50000 : ℝ)=(1000145079007053/1000000000000000 : ℝ) by norm_num, show 1+2*(15682877265908823/50000000000000000000 : ℝ)=(25015682877265908823/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23749520881030978617/23755000000000000000 : ℝ)*(X 1 0+X 2 0)+(576804367427/475100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (23749520881030978617/23755000000000000000 : ℝ)) (alpha := (576804367427/475100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23749520881030978617/23755000000000000000 : ℝ)*(X 0 1+X 2 1)+(576804367427/475100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (23749520881030978617/23755000000000000000 : ℝ)) (alpha := (576804367427/475100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23749520881030978617/23755000000000000000 : ℝ)*(X 0 2+X 1 2)+(576804367427/475100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (23749520881030978617/23755000000000000000 : ℝ)) (alpha := (576804367427/475100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-121135989/625000000 : ℝ)*X 0 0+(543928771/1000000000 : ℝ)*X 0 1+(5214950957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677009893/5000000000 : ℝ)*X 1 0+(-2053182973/10000000000 : ℝ)*X 1 1+(2607475467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354019753/10000000000 : ℝ)*X 2 0+(1042990199/2000000000 : ℝ)*X 2 1+(-256647867/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291685419/10000000000 : ℝ)*X 0 0+(4051785321/10000000000 : ℝ)*X 0 1+(181761741/400000000 : ℝ)*X 0 2+(4291685419/10000000000 : ℝ)*X 1 0+(4051785321/10000000000 : ℝ)*X 1 1+(181761741/400000000 : ℝ)*X 1 2+(4291685419/10000000000 : ℝ)*X 2 0+(4051785321/10000000000 : ℝ)*X 2 1+(181761741/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1938206849/10000000000 : ℝ)*X 0 0+(5216095597/10000000000 : ℝ)*X 0 1+(1087626931/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295575579/10000000000 : ℝ)*X 1 0+(-914999617/5000000000 : ℝ)*X 1 1+(2719067339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647787797/5000000000 : ℝ)*X 2 0+(1359533673/2500000000 : ℝ)*X 2 1+(-1829999193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4291753491/10000000000 : ℝ)*X 0 0+(90830637/200000000 : ℝ)*X 0 1+(20271577/50000000 : ℝ)*X 0 2+(4291753491/10000000000 : ℝ)*X 1 0+(90830637/200000000 : ℝ)*X 1 1+(20271577/50000000 : ℝ)*X 1 2+(4291753491/10000000000 : ℝ)*X 2 0+(90830637/200000000 : ℝ)*X 2 1+(20271577/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (832856994120851653004894091/118775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (627172403/50000000000000 : ℝ)*(base19) + (1163311943/100000000000000 : ℝ)*(base23) + (34029023/100000000000000 : ℝ)*(lower2) + (160934869/100000000000000 : ℝ)*(upper3) + (143287327/100000000000000 : ℝ)*(upper5) + (648909493094241/20000000000000 : ℝ)*(major0) + (648909493094241/20000000000000 : ℝ)*(major1) + (1622273732735603/50000000000000 : ℝ)*(major2) + (2228801718053291/50000000000000 : ℝ)*(sp0) + (2228810702307421/50000000000000 : ℝ)*(sp1) + (557202686955963/12500000000000 : ℝ)*(sp2) + (2031462919559057/100000000000000 : ℝ)*(sp3) + (9611426533/50000000000000 : ℝ)*(sp4) + (1139836061/12500000000000 : ℝ)*(sp7) + (406294407649509/20000000000000 : ℝ)*(f.failure) + (139300708092489/3125000000000 : ℝ)*(f.sum) + (19120328769893/47510000000000000000000000000 : ℝ)*base66 + (3832066222090435303/475100000000000000000000000000000 : ℝ)*base68 + (687620053173773949/1187750000000000000000000000000000 : ℝ)*base70 + (2296525245748835303/475100000000000000000000000000000 : ℝ)*base72 + (86479101324313/47510000000000000000000000000 : ℝ)*base74 + (1859318328020226051/1187750000000000000000000000000000 : ℝ)*base75 + (4662510890253105303/475100000000000000000000000000000 : ℝ)*base78 + (4351421099100505303/475100000000000000000000000000000 : ℝ)*base80 + (581402141997/593875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (14222481/2000000000000000000000 : ℝ)*base89 + (14222481/2000000000000000000000 : ℝ)*base91 + (5777519/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (809080619590527943199211519/74234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117175583/6250000000000 : ℝ)*(base19) + (2030100649/100000000000000 : ℝ)*(base23) + (616052277/100000000000000 : ℝ)*(lower1) + (124784479/50000000000000 : ℝ)*(upper3) + (28936413/50000000000000 : ℝ)*(lower4) + (229869113/100000000000000 : ℝ)*(upper5) + (204879581795369/6250000000000 : ℝ)*(major0) + (204879581795369/6250000000000 : ℝ)*(major1) + (204879581795369/6250000000000 : ℝ)*(major2) + (3012678181/100000000000000 : ℝ)*(sp2) + (4503683056472737/100000000000000 : ℝ)*(sp4) + (450368118166341/10000000000000 : ℝ)*(sp5) + (4503678013693907/100000000000000 : ℝ)*(sp6) + (513115799419747/25000000000000 : ℝ)*(sp7) + (513115799419747/25000000000000 : ℝ)*(f.failure) + (4503683056472737/100000000000000 : ℝ)*(f.sum) + (37565327759217/23755000000000000000000000000 : ℝ)*base66 + (2535539107767569077/148468750000000000000000000000000 : ℝ)*base68 + (163900653162756577/148468750000000000000000000000000 : ℝ)*base70 + (1463966603781912827/148468750000000000000000000000000 : ℝ)*base72 + (4144454338677/5938750000000000000000000000 : ℝ)*base73 + (3801731145193850327/148468750000000000000000000000000 : ℝ)*base76 + (672802971517743423/148468750000000000000000000000000 : ℝ)*base77 + (652051883318368423/148468750000000000000000000000000 : ℝ)*base79 + (95667856573407/23755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9110423/2500000000000000000000 : ℝ)*base89 + (9110423/2500000000000000000000 : ℝ)*base91 + (9110423/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1466_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (967/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1466_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1466_s7_0 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338503897/2500000000 : ℝ)*x 0 + (5214964879/10000000000 : ℝ)*x 1 + (-513292529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338503897/2500000000 : ℝ)^4429 ≤ (22184738694009/50000000000000 : ℝ)^3405 := by
    have hnat : (1338503897 : ℕ)^4429*50000000000000^3405 ≤ 22184738694009^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338503897 2500000000 22184738694009 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214964879/10000000000 : ℝ)^4429 ≤ (21438244050301/50000000000000 : ℝ)^3405 := by
    have hnat : (5214964879 : ℕ)^4429*50000000000000^3405 ≤ 21438244050301^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214964879 10000000000 21438244050301 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513292529/2500000000 : ℝ)^4429 ≤ (12754034495699/100000000000000 : ℝ)^3405 := by
    have hnat : (513292529 : ℕ)^4429*100000000000000^3405 ≤ 12754034495699^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513292529 2500000000 12754034495699 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338503897/2500000000 : ℝ), (5214964879/10000000000 : ℝ), (-513292529/2500000000 : ℝ)] ![(22184738694009/50000000000000 : ℝ), (21438244050301/50000000000000 : ℝ), (12754034495699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338503897/2500000000 : ℝ)|^4429 ≤ (22184738694009/50000000000000 : ℝ)^3405
        have hw : |(1338503897/2500000000 : ℝ)|=(1338503897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214964879/10000000000 : ℝ)|^4429 ≤ (21438244050301/50000000000000 : ℝ)^3405
        have hw : |(5214964879/10000000000 : ℝ)|=(5214964879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513292529/2500000000 : ℝ)|^4429 ≤ (12754034495699/100000000000000 : ℝ)^3405
        have hw : |(-513292529/2500000000 : ℝ)|=(513292529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s7_1 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072921679/2500000000 : ℝ)*x 0 + (2025906109/5000000000 : ℝ)*x 1 + (568002033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072921679/2500000000 : ℝ)^4429 ≤ (33277193008739/100000000000000 : ℝ)^3405 := by
    have hnat : (1072921679 : ℕ)^4429*100000000000000^3405 ≤ 33277193008739^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072921679 2500000000 33277193008739 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025906109/5000000000 : ℝ)^4429 ≤ (30878488470371/100000000000000 : ℝ)^3405 := by
    have hnat : (2025906109 : ℕ)^4429*100000000000000^3405 ≤ 30878488470371^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025906109 5000000000 30878488470371 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568002033/1250000000 : ℝ)^4429 ≤ (35844318504187/100000000000000 : ℝ)^3405 := by
    have hnat : (568002033 : ℕ)^4429*100000000000000^3405 ≤ 35844318504187^3405*1250000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568002033 1250000000 35844318504187 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072921679/2500000000 : ℝ), (2025906109/5000000000 : ℝ), (568002033/1250000000 : ℝ)] ![(33277193008739/100000000000000 : ℝ), (30878488470371/100000000000000 : ℝ), (35844318504187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072921679/2500000000 : ℝ)|^4429 ≤ (33277193008739/100000000000000 : ℝ)^3405
        have hw : |(1072921679/2500000000 : ℝ)|=(1072921679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2025906109/5000000000 : ℝ)|^4429 ≤ (30878488470371/100000000000000 : ℝ)^3405
        have hw : |(2025906109/5000000000 : ℝ)|=(2025906109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568002033/1250000000 : ℝ)|^4429 ≤ (35844318504187/100000000000000 : ℝ)^3405
        have hw : |(568002033/1250000000 : ℝ)|=(568002033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s7_2 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-484552061/2500000000 : ℝ)*x 0 + (521610819/1000000000 : ℝ)*x 1 + (1359530299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (484552061/2500000000 : ℝ)^4429 ≤ (11833068172099/100000000000000 : ℝ)^3405 := by
    have hnat : (484552061 : ℕ)^4429*100000000000000^3405 ≤ 11833068172099^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484552061 2500000000 11833068172099 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521610819/1000000000 : ℝ)^4429 ≤ (21444357763823/50000000000000 : ℝ)^3405 := by
    have hnat : (521610819 : ℕ)^4429*50000000000000^3405 ≤ 21444357763823^3405*1000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521610819 1000000000 21444357763823 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359530299/2500000000 : ℝ)^4429 ≤ (45278216280001/100000000000000 : ℝ)^3405 := by
    have hnat : (1359530299 : ℕ)^4429*100000000000000^3405 ≤ 45278216280001^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359530299 2500000000 45278216280001 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-484552061/2500000000 : ℝ), (521610819/1000000000 : ℝ), (1359530299/2500000000 : ℝ)] ![(11833068172099/100000000000000 : ℝ), (21444357763823/50000000000000 : ℝ), (45278216280001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-484552061/2500000000 : ℝ)|^4429 ≤ (11833068172099/100000000000000 : ℝ)^3405
        have hw : |(-484552061/2500000000 : ℝ)|=(484552061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521610819/1000000000 : ℝ)|^4429 ≤ (21444357763823/50000000000000 : ℝ)^3405
        have hw : |(521610819/1000000000 : ℝ)|=(521610819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359530299/2500000000 : ℝ)|^4429 ≤ (45278216280001/100000000000000 : ℝ)^3405
        have hw : |(1359530299/2500000000 : ℝ)|=(1359530299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s7_3 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647789461/5000000000 : ℝ)*x 0 + (-1830013447/10000000000 : ℝ)*x 1 + (5438121119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647789461/5000000000 : ℝ)^4429 ≤ (2187030179049/5000000000000 : ℝ)^3405 := by
    have hnat : (2647789461 : ℕ)^4429*5000000000000^3405 ≤ 2187030179049^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647789461 5000000000 2187030179049 5000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1830013447/10000000000 : ℝ)^4429 ≤ (10981180964327/100000000000000 : ℝ)^3405 := by
    have hnat : (1830013447 : ℕ)^4429*100000000000000^3405 ≤ 10981180964327^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830013447 10000000000 10981180964327 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438121119/10000000000 : ℝ)^4429 ≤ (4527821544609/10000000000000 : ℝ)^3405 := by
    have hnat : (5438121119 : ℕ)^4429*10000000000000^3405 ≤ 4527821544609^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438121119 10000000000 4527821544609 10000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647789461/5000000000 : ℝ), (-1830013447/10000000000 : ℝ), (5438121119/10000000000 : ℝ)] ![(2187030179049/5000000000000 : ℝ), (10981180964327/100000000000000 : ℝ), (4527821544609/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647789461/5000000000 : ℝ)|^4429 ≤ (2187030179049/5000000000000 : ℝ)^3405
        have hw : |(2647789461/5000000000 : ℝ)|=(2647789461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1830013447/10000000000 : ℝ)|^4429 ≤ (10981180964327/100000000000000 : ℝ)^3405
        have hw : |(-1830013447/10000000000 : ℝ)|=(1830013447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438121119/10000000000 : ℝ)|^4429 ≤ (4527821544609/10000000000000 : ℝ)^3405
        have hw : |(5438121119/10000000000 : ℝ)|=(5438121119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s7_4 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323894717/2500000000 : ℝ)*x 0 + (1087624241/2000000000 : ℝ)*x 1 + (-1830013401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323894717/2500000000 : ℝ)^4429 ≤ (10935150750203/25000000000000 : ℝ)^3405 := by
    have hnat : (1323894717 : ℕ)^4429*25000000000000^3405 ≤ 10935150750203^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323894717 2500000000 10935150750203 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087624241/2000000000 : ℝ)^4429 ≤ (45278216377471/100000000000000 : ℝ)^3405 := by
    have hnat : (1087624241 : ℕ)^4429*100000000000000^3405 ≤ 45278216377471^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087624241 2000000000 45278216377471 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1830013401/10000000000 : ℝ)^4429 ≤ (1372647575661/12500000000000 : ℝ)^3405 := by
    have hnat : (1830013401 : ℕ)^4429*12500000000000^3405 ≤ 1372647575661^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830013401 10000000000 1372647575661 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323894717/2500000000 : ℝ), (1087624241/2000000000 : ℝ), (-1830013401/10000000000 : ℝ)] ![(10935150750203/25000000000000 : ℝ), (45278216377471/100000000000000 : ℝ), (1372647575661/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323894717/2500000000 : ℝ)|^4429 ≤ (10935150750203/25000000000000 : ℝ)^3405
        have hw : |(1323894717/2500000000 : ℝ)|=(1323894717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087624241/2000000000 : ℝ)|^4429 ≤ (45278216377471/100000000000000 : ℝ)^3405
        have hw : |(1087624241/2000000000 : ℝ)|=(1087624241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1830013401/10000000000 : ℝ)|^4429 ≤ (1372647575661/12500000000000 : ℝ)^3405
        have hw : |(-1830013401/10000000000 : ℝ)|=(1830013401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_s7_5 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072938419/2500000000 : ℝ)*x 0 + (4541503931/10000000000 : ℝ)*x 1 + (40543441/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072938419/2500000000 : ℝ)^4429 ≤ (33277868350649/100000000000000 : ℝ)^3405 := by
    have hnat : (1072938419 : ℕ)^4429*100000000000000^3405 ≤ 33277868350649^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072938419 2500000000 33277868350649 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4541503931/10000000000 : ℝ)^4429 ≤ (8954635706427/25000000000000 : ℝ)^3405 := by
    have hnat : (4541503931 : ℕ)^4429*25000000000000^3405 ≤ 8954635706427^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541503931 10000000000 8954635706427 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40543441/100000000 : ℝ)^4429 ≤ (15451794403543/50000000000000 : ℝ)^3405 := by
    have hnat : (40543441 : ℕ)^4429*50000000000000^3405 ≤ 15451794403543^3405*100000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40543441 100000000 15451794403543 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072938419/2500000000 : ℝ), (4541503931/10000000000 : ℝ), (40543441/100000000 : ℝ)] ![(33277868350649/100000000000000 : ℝ), (8954635706427/25000000000000 : ℝ), (15451794403543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072938419/2500000000 : ℝ)|^4429 ≤ (33277868350649/100000000000000 : ℝ)^3405
        have hw : |(1072938419/2500000000 : ℝ)|=(1072938419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4541503931/10000000000 : ℝ)|^4429 ≤ (8954635706427/25000000000000 : ℝ)^3405
        have hw : |(4541503931/10000000000 : ℝ)|=(4541503931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40543441/100000000 : ℝ)|^4429 ≤ (15451794403543/50000000000000 : ℝ)^3405
        have hw : |(40543441/100000000 : ℝ)|=(40543441/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1466_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (429/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15471/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (429/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (967/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (429/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (429/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (967/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (429/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (429/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (967/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (429/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (429/4000 : ℝ) ^ (4427/1024 : ℝ) ≤ (401839591162521/6250000000000000000 : ℝ) := by
    have hpowers : (429/4000 : ℝ)^4427 ≤ (401839591162521/6250000000000000000 : ℝ)^1024 := by
      have hnat : (429 : ℕ)^4427*6250000000000000000^1024 ≤ 401839591162521^1024*4000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        429 4000 401839591162521 6250000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (429/4000 : ℝ)) (X := (401839591162521/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (967/6250 : ℝ) ^ (4427/1024 : ℝ) ≤ (244908061686901/781250000000000000 : ℝ) := by
    have hpowers : (967/6250 : ℝ)^4427 ≤ (244908061686901/781250000000000000 : ℝ)^1024 := by
      have hnat : (967 : ℕ)^4427*781250000000000000^1024 ≤ 244908061686901^1024*6250^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 6250 244908061686901 781250000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/6250 : ℝ)) (X := (244908061686901/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125401839591162521/3125000000000000000 : ℝ) ≤ (2500074355257523/2500000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (3125401839591162521/3125000000000000000 : ℝ)^1024 ≤ (2500074355257523/2500000000000000 : ℝ)^4427 := by
      have hnat : (3125401839591162521 : ℕ)^1024*2500000000000000^4427 ≤ 2500074355257523^4427*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125401839591162521 3125000000000000000 2500074355257523 2500000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074355257523/2500000000000000 : ℝ)) (X := (3125401839591162521/3125000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252361104084657729/6250000000000000000 : ℝ) ≤ (200017474006653/200000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (6252361104084657729/6250000000000000000 : ℝ)^1024 ≤ (200017474006653/200000000000000 : ℝ)^4427 := by
      have hnat : (6252361104084657729 : ℕ)^1024*200000000000000^4427 ≤ 200017474006653^4427*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252361104084657729 6250000000000000000 200017474006653 200000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200017474006653/200000000000000 : ℝ)) (X := (6252361104084657729/6250000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (390869908061686901/390625000000000000 : ℝ) ≤ (1250181247454401/1250000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (390869908061686901/390625000000000000 : ℝ)^1024 ≤ (1250181247454401/1250000000000000 : ℝ)^4427 := by
      have hnat : (390869908061686901 : ℕ)^1024*1250000000000000^4427 ≤ 1250181247454401^4427*390625000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390869908061686901 390625000000000000 1250181247454401 1250000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250181247454401/1250000000000000 : ℝ)) (X := (390869908061686901/390625000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(401839591162521/6250000000000000000 : ℝ) ≤ ((5932381333323747203/5933750000000000000 : ℝ)+2*(288139651279/237350000000000 : ℝ)*(429/4000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (5932381333323747203/5933750000000000000 : ℝ)+2*(288139651279/237350000000000 : ℝ)*(429/4000 : ℝ)=(2500074355257523/2500000000000000 : ℝ) by norm_num, show 1+2*(401839591162521/6250000000000000000 : ℝ)=(3125401839591162521/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(244908061686901/781250000000000000 : ℝ)+(401839591162521/6250000000000000000 : ℝ) ≤ ((5932381333323747203/5933750000000000000 : ℝ)+(288139651279/237350000000000 : ℝ)*((967/6250 : ℝ)+(429/4000 : ℝ)))^(4427/1024 : ℝ) := by
    rw [show (5932381333323747203/5933750000000000000 : ℝ)+(288139651279/237350000000000 : ℝ)*((967/6250 : ℝ)+(429/4000 : ℝ))=(200017474006653/200000000000000 : ℝ) by norm_num, show 1+(244908061686901/781250000000000000 : ℝ)+(401839591162521/6250000000000000000 : ℝ)=(6252361104084657729/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(244908061686901/781250000000000000 : ℝ) ≤ ((5932381333323747203/5933750000000000000 : ℝ)+2*(288139651279/237350000000000 : ℝ)*(967/6250 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (5932381333323747203/5933750000000000000 : ℝ)+2*(288139651279/237350000000000 : ℝ)*(967/6250 : ℝ)=(1250181247454401/1250000000000000 : ℝ) by norm_num, show 1+2*(244908061686901/781250000000000000 : ℝ)=(390869908061686901/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5932381333323747203/5933750000000000000 : ℝ)*(X 1 0+X 2 0)+(288139651279/237350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (5932381333323747203/5933750000000000000 : ℝ)) (alpha := (288139651279/237350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5932381333323747203/5933750000000000000 : ℝ)*(X 0 1+X 2 1)+(288139651279/237350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (5932381333323747203/5933750000000000000 : ℝ)) (alpha := (288139651279/237350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5932381333323747203/5933750000000000000 : ℝ)*(X 0 2+X 1 2)+(288139651279/237350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (967/6250 : ℝ)) (c := (5932381333323747203/5933750000000000000 : ℝ)) (alpha := (288139651279/237350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1338503897/2500000000 : ℝ)*X 2 0+(5214964879/10000000000 : ℝ)*X 2 1+(-513292529/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072921679/2500000000 : ℝ)*X 0 0+(2025906109/5000000000 : ℝ)*X 0 1+(568002033/1250000000 : ℝ)*X 0 2+(1072921679/2500000000 : ℝ)*X 1 0+(2025906109/5000000000 : ℝ)*X 1 1+(568002033/1250000000 : ℝ)*X 1 2+(1072921679/2500000000 : ℝ)*X 2 0+(2025906109/5000000000 : ℝ)*X 2 1+(568002033/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s7_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-484552061/2500000000 : ℝ)*X 0 0+(521610819/1000000000 : ℝ)*X 0 1+(1359530299/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s7_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2647789461/5000000000 : ℝ)*X 1 0+(-1830013447/10000000000 : ℝ)*X 1 1+(5438121119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s7_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1323894717/2500000000 : ℝ)*X 2 0+(1087624241/2000000000 : ℝ)*X 2 1+(-1830013401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s7_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072938419/2500000000 : ℝ)*X 0 0+(4541503931/10000000000 : ℝ)*X 0 1+(40543441/100000000 : ℝ)*X 0 2+(1072938419/2500000000 : ℝ)*X 1 0+(4541503931/10000000000 : ℝ)*X 1 1+(40543441/100000000 : ℝ)*X 1 2+(1072938419/2500000000 : ℝ)*X 2 0+(4541503931/10000000000 : ℝ)*X 2 1+(40543441/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87934716472142072799009939/14834375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43755243/100000000000000 : ℝ)*(base19) + (2065087/100000000000000 : ℝ)*(upper2) + (736101/5000000000000 : ℝ)*(lower3) + (8905119/50000000000000 : ℝ)*(upper4) + (121278427/100000000000000 : ℝ)*(lower5) + (327847702622371/10000000000000 : ℝ)*(major0) + (327847702622371/10000000000000 : ℝ)*(major1) + (327847702622371/10000000000000 : ℝ)*(major2) + (1445760831/50000000000000 : ℝ)*(sp0) + (111789847/50000000000000 : ℝ)*(sp1) + (225211894103839/5000000000000 : ℝ)*(sp2) + (4504237838321537/100000000000000 : ℝ)*(sp3) + (2252117495277559/50000000000000 : ℝ)*(sp4) + (205271574919871/10000000000000 : ℝ)*(sp5) + (513178993194601/25000000000000 : ℝ)*(f.failure) + (225211894103839/5000000000000 : ℝ)*(f.sum) + (1765525637083/1186750000000000000000000000 : ℝ)*base66 + (334309678423221687/59337500000000000000000000000000 : ℝ)*base68 + (712415621519696687/59337500000000000000000000000000 : ℝ)*base70 + (379016820969628313/59337500000000000000000000000000 : ℝ)*base71 + (244585994703/189880000000000000000000000 : ℝ)*base73 + (834342970596959187/59337500000000000000000000000000 : ℝ)*base76 + (1321706923740396687/59337500000000000000000000000000 : ℝ)*base78 + (319354129602421687/59337500000000000000000000000000 : ℝ)*base80 + (1943029204073/2373500000000000000000000000 : ℝ)*base82 + (12325509/2500000000000000000000 : ℝ)*base89 + (12325509/2500000000000000000000 : ℝ)*base91 + (12325509/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1466_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (967/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15471/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1466_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1466_box_0 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1715939313/10000000000 : ℝ)*x 0 + (5407822913/10000000000 : ℝ)*x 1 + (337988917/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1715939313/10000000000 : ℝ)^4429 ≤ (10099281133631/100000000000000 : ℝ)^3405 := by
    have hnat : (1715939313 : ℕ)^4429*100000000000000^3405 ≤ 10099281133631^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715939313 10000000000 10099281133631 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407822913/10000000000 : ℝ)^4429 ≤ (44950360725217/100000000000000 : ℝ)^3405 := by
    have hnat : (5407822913 : ℕ)^4429*100000000000000^3405 ≤ 44950360725217^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407822913 10000000000 44950360725217 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337988917/625000000 : ℝ)^4429 ≤ (8990071623913/20000000000000 : ℝ)^3405 := by
    have hnat : (337988917 : ℕ)^4429*20000000000000^3405 ≤ 8990071623913^3405*625000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337988917 625000000 8990071623913 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1715939313/10000000000 : ℝ), (5407822913/10000000000 : ℝ), (337988917/625000000 : ℝ)] ![(10099281133631/100000000000000 : ℝ), (44950360725217/100000000000000 : ℝ), (8990071623913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1715939313/10000000000 : ℝ)|^4429 ≤ (10099281133631/100000000000000 : ℝ)^3405
        have hw : |(-1715939313/10000000000 : ℝ)|=(1715939313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407822913/10000000000 : ℝ)|^4429 ≤ (44950360725217/100000000000000 : ℝ)^3405
        have hw : |(5407822913/10000000000 : ℝ)|=(5407822913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337988917/625000000 : ℝ)|^4429 ≤ (8990071623913/20000000000000 : ℝ)^3405
        have hw : |(337988917/625000000 : ℝ)|=(337988917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_1 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053981459/2000000000 : ℝ)*x 0 + (-1906849441/10000000000 : ℝ)*x 1 + (2703911287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053981459/2000000000 : ℝ)^4429 ≤ (5433124097341/12500000000000 : ℝ)^3405 := by
    have hnat : (1053981459 : ℕ)^4429*12500000000000^3405 ≤ 5433124097341^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053981459 2000000000 5433124097341 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906849441/10000000000 : ℝ)^4429 ≤ (11584650151639/100000000000000 : ℝ)^3405 := by
    have hnat : (1906849441 : ℕ)^4429*100000000000000^3405 ≤ 11584650151639^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906849441 10000000000 11584650151639 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703911287/5000000000 : ℝ)^4429 ≤ (22475178530003/50000000000000 : ℝ)^3405 := by
    have hnat : (2703911287 : ℕ)^4429*50000000000000^3405 ≤ 22475178530003^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703911287 5000000000 22475178530003 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053981459/2000000000 : ℝ), (-1906849441/10000000000 : ℝ), (2703911287/5000000000 : ℝ)] ![(5433124097341/12500000000000 : ℝ), (11584650151639/100000000000000 : ℝ), (22475178530003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053981459/2000000000 : ℝ)|^4429 ≤ (5433124097341/12500000000000 : ℝ)^3405
        have hw : |(1053981459/2000000000 : ℝ)|=(1053981459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906849441/10000000000 : ℝ)|^4429 ≤ (11584650151639/100000000000000 : ℝ)^3405
        have hw : |(-1906849441/10000000000 : ℝ)|=(1906849441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703911287/5000000000 : ℝ)|^4429 ≤ (22475178530003/50000000000000 : ℝ)^3405
        have hw : |(2703911287/5000000000 : ℝ)|=(2703911287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_2 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317476747/2500000000 : ℝ)*x 0 + (2703911521/5000000000 : ℝ)*x 1 + (-1906849217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317476747/2500000000 : ℝ)^4429 ≤ (43464989485183/100000000000000 : ℝ)^3405 := by
    have hnat : (1317476747 : ℕ)^4429*100000000000000^3405 ≤ 43464989485183^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317476747 2500000000 43464989485183 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703911521/5000000000 : ℝ)^4429 ≤ (44950362119943/100000000000000 : ℝ)^3405 := by
    have hnat : (2703911521 : ℕ)^4429*100000000000000^3405 ≤ 44950362119943^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703911521 5000000000 44950362119943 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906849217/10000000000 : ℝ)^4429 ≤ (11584648381517/100000000000000 : ℝ)^3405 := by
    have hnat : (1906849217 : ℕ)^4429*100000000000000^3405 ≤ 11584648381517^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906849217 10000000000 11584648381517 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317476747/2500000000 : ℝ), (2703911521/5000000000 : ℝ), (-1906849217/10000000000 : ℝ)] ![(43464989485183/100000000000000 : ℝ), (44950362119943/100000000000000 : ℝ), (11584648381517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317476747/2500000000 : ℝ)|^4429 ≤ (43464989485183/100000000000000 : ℝ)^3405
        have hw : |(1317476747/2500000000 : ℝ)|=(1317476747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703911521/5000000000 : ℝ)|^4429 ≤ (44950362119943/100000000000000 : ℝ)^3405
        have hw : |(2703911521/5000000000 : ℝ)|=(2703911521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906849217/10000000000 : ℝ)|^4429 ≤ (11584648381517/100000000000000 : ℝ)^3405
        have hw : |(-1906849217/10000000000 : ℝ)|=(1906849217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_3 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1124255083/2500000000 : ℝ)*x 0 + (26226989/62500000 : ℝ)*x 1 + (65567481/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124255083/2500000000 : ℝ)^4429 ≤ (8840716978569/25000000000000 : ℝ)^3405 := by
    have hnat : (1124255083 : ℕ)^4429*25000000000000^3405 ≤ 8840716978569^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124255083 2500000000 8840716978569 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26226989/62500000 : ℝ)^4429 ≤ (32318563306287/100000000000000 : ℝ)^3405 := by
    have hnat : (26226989 : ℕ)^4429*100000000000000^3405 ≤ 32318563306287^3405*62500000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26226989 62500000 32318563306287 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65567481/156250000 : ℝ)^4429 ≤ (126244409203/390625000000 : ℝ)^3405 := by
    have hnat : (65567481 : ℕ)^4429*390625000000^3405 ≤ 126244409203^3405*156250000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65567481 156250000 126244409203 390625000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124255083/2500000000 : ℝ), (26226989/62500000 : ℝ), (65567481/156250000 : ℝ)] ![(8840716978569/25000000000000 : ℝ), (32318563306287/100000000000000 : ℝ), (126244409203/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124255083/2500000000 : ℝ)|^4429 ≤ (8840716978569/25000000000000 : ℝ)^3405
        have hw : |(1124255083/2500000000 : ℝ)|=(1124255083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26226989/62500000 : ℝ)|^4429 ≤ (32318563306287/100000000000000 : ℝ)^3405
        have hw : |(26226989/62500000 : ℝ)|=(26226989/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65567481/156250000 : ℝ)|^4429 ≤ (126244409203/390625000000 : ℝ)^3405
        have hw : |(65567481/156250000 : ℝ)|=(65567481/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_4 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86635867/400000000 : ℝ)*x 0 + (209672587/400000000 : ℝ)*x 1 + (5241815101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86635867/400000000 : ℝ)^4429 ≤ (13672290286087/100000000000000 : ℝ)^3405 := by
    have hnat : (86635867 : ℕ)^4429*100000000000000^3405 ≤ 13672290286087^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86635867 400000000 13672290286087 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209672587/400000000 : ℝ)^4429 ≤ (8632770513091/20000000000000 : ℝ)^3405 := by
    have hnat : (209672587 : ℕ)^4429*20000000000000^3405 ≤ 8632770513091^3405*400000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209672587 400000000 8632770513091 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241815101/10000000000 : ℝ)^4429 ≤ (4316385712831/10000000000000 : ℝ)^3405 := by
    have hnat : (5241815101 : ℕ)^4429*10000000000000^3405 ≤ 4316385712831^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241815101 10000000000 4316385712831 10000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86635867/400000000 : ℝ), (209672587/400000000 : ℝ), (5241815101/10000000000 : ℝ)] ![(13672290286087/100000000000000 : ℝ), (8632770513091/20000000000000 : ℝ), (4316385712831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86635867/400000000 : ℝ)|^4429 ≤ (13672290286087/100000000000000 : ℝ)^3405
        have hw : |(-86635867/400000000 : ℝ)|=(86635867/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209672587/400000000 : ℝ)|^4429 ≤ (8632770513091/20000000000000 : ℝ)^3405
        have hw : |(209672587/400000000 : ℝ)|=(209672587/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241815101/10000000000 : ℝ)|^4429 ≤ (4316385712831/10000000000000 : ℝ)^3405
        have hw : |(5241815101/10000000000 : ℝ)|=(5241815101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_5 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692952239/5000000000 : ℝ)*x 0 + (-1974568017/10000000000 : ℝ)*x 1 + (5241814829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692952239/5000000000 : ℝ)^4429 ≤ (11178381713709/25000000000000 : ℝ)^3405 := by
    have hnat : (2692952239 : ℕ)^4429*25000000000000^3405 ≤ 11178381713709^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692952239 5000000000 11178381713709 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1974568017/10000000000 : ℝ)^4429 ≤ (3030654730601/25000000000000 : ℝ)^3405 := by
    have hnat : (1974568017 : ℕ)^4429*25000000000000^3405 ≤ 3030654730601^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974568017 10000000000 3030654730601 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241814829/10000000000 : ℝ)^4429 ≤ (21581927107469/50000000000000 : ℝ)^3405 := by
    have hnat : (5241814829 : ℕ)^4429*50000000000000^3405 ≤ 21581927107469^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241814829 10000000000 21581927107469 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692952239/5000000000 : ℝ), (-1974568017/10000000000 : ℝ), (5241814829/10000000000 : ℝ)] ![(11178381713709/25000000000000 : ℝ), (3030654730601/25000000000000 : ℝ), (21581927107469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692952239/5000000000 : ℝ)|^4429 ≤ (11178381713709/25000000000000 : ℝ)^3405
        have hw : |(2692952239/5000000000 : ℝ)|=(2692952239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1974568017/10000000000 : ℝ)|^4429 ≤ (3030654730601/25000000000000 : ℝ)^3405
        have hw : |(-1974568017/10000000000 : ℝ)|=(1974568017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241814829/10000000000 : ℝ)|^4429 ≤ (21581927107469/50000000000000 : ℝ)^3405
        have hw : |(5241814829/10000000000 : ℝ)|=(5241814829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_6 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346476151/2500000000 : ℝ)*x 0 + (1048362981/2000000000 : ℝ)*x 1 + (-1974567743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346476151/2500000000 : ℝ)^4429 ≤ (5589191026933/12500000000000 : ℝ)^3405 := by
    have hnat : (1346476151 : ℕ)^4429*12500000000000^3405 ≤ 5589191026933^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346476151 2500000000 5589191026933 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048362981/2000000000 : ℝ)^4429 ≤ (43163855028969/100000000000000 : ℝ)^3405 := by
    have hnat : (1048362981 : ℕ)^4429*100000000000000^3405 ≤ 43163855028969^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048362981 2000000000 43163855028969 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1974567743/10000000000 : ℝ)^4429 ≤ (6061308367161/50000000000000 : ℝ)^3405 := by
    have hnat : (1974567743 : ℕ)^4429*50000000000000^3405 ≤ 6061308367161^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974567743 10000000000 6061308367161 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346476151/2500000000 : ℝ), (1048362981/2000000000 : ℝ), (-1974567743/10000000000 : ℝ)] ![(5589191026933/12500000000000 : ℝ), (43163855028969/100000000000000 : ℝ), (6061308367161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346476151/2500000000 : ℝ)|^4429 ≤ (5589191026933/12500000000000 : ℝ)^3405
        have hw : |(1346476151/2500000000 : ℝ)|=(1346476151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048362981/2000000000 : ℝ)|^4429 ≤ (43163855028969/100000000000000 : ℝ)^3405
        have hw : |(1048362981/2000000000 : ℝ)|=(1048362981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1974567743/10000000000 : ℝ)|^4429 ≤ (6061308367161/50000000000000 : ℝ)^3405
        have hw : |(-1974567743/10000000000 : ℝ)|=(1974567743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_7 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4084165957/10000000000 : ℝ)*x 0 + (2201302373/5000000000 : ℝ)*x 1 + (2201302597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4084165957/10000000000 : ℝ)^4429 ≤ (31199588196981/100000000000000 : ℝ)^3405 := by
    have hnat : (4084165957 : ℕ)^4429*100000000000000^3405 ≤ 31199588196981^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4084165957 10000000000 31199588196981 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201302373/5000000000 : ℝ)^4429 ≤ (4300025451959/12500000000000 : ℝ)^3405 := by
    have hnat : (2201302373 : ℕ)^4429*12500000000000^3405 ≤ 4300025451959^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201302373 5000000000 4300025451959 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201302597/5000000000 : ℝ)^4429 ≤ (8600052042221/25000000000000 : ℝ)^3405 := by
    have hnat : (2201302597 : ℕ)^4429*25000000000000^3405 ≤ 8600052042221^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201302597 5000000000 8600052042221 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4084165957/10000000000 : ℝ), (2201302373/5000000000 : ℝ), (2201302597/5000000000 : ℝ)] ![(31199588196981/100000000000000 : ℝ), (4300025451959/12500000000000 : ℝ), (8600052042221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4084165957/10000000000 : ℝ)|^4429 ≤ (31199588196981/100000000000000 : ℝ)^3405
        have hw : |(4084165957/10000000000 : ℝ)|=(4084165957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201302373/5000000000 : ℝ)|^4429 ≤ (4300025451959/12500000000000 : ℝ)^3405
        have hw : |(2201302373/5000000000 : ℝ)|=(2201302373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2201302597/5000000000 : ℝ)|^4429 ≤ (8600052042221/25000000000000 : ℝ)^3405
        have hw : |(2201302597/5000000000 : ℝ)|=(2201302597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_8 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414216967/2000000000 : ℝ)*x 0 + (5126044851/10000000000 : ℝ)*x 1 + (5428406599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414216967/2000000000 : ℝ)^4429 ≤ (12898974907371/100000000000000 : ℝ)^3405 := by
    have hnat : (414216967 : ℕ)^4429*100000000000000^3405 ≤ 12898974907371^3405*2000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414216967 2000000000 12898974907371 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126044851/10000000000 : ℝ)^4429 ≤ (41927989735963/100000000000000 : ℝ)^3405 := by
    have hnat : (5126044851 : ℕ)^4429*100000000000000^3405 ≤ 41927989735963^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126044851 10000000000 41927989735963 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428406599/10000000000 : ℝ)^4429 ≤ (1411657354293/3125000000000 : ℝ)^3405 := by
    have hnat : (5428406599 : ℕ)^4429*3125000000000^3405 ≤ 1411657354293^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428406599 10000000000 1411657354293 3125000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414216967/2000000000 : ℝ), (5126044851/10000000000 : ℝ), (5428406599/10000000000 : ℝ)] ![(12898974907371/100000000000000 : ℝ), (41927989735963/100000000000000 : ℝ), (1411657354293/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414216967/2000000000 : ℝ)|^4429 ≤ (12898974907371/100000000000000 : ℝ)^3405
        have hw : |(-414216967/2000000000 : ℝ)|=(414216967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126044851/10000000000 : ℝ)|^4429 ≤ (41927989735963/100000000000000 : ℝ)^3405
        have hw : |(5126044851/10000000000 : ℝ)|=(5126044851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428406599/10000000000 : ℝ)|^4429 ≤ (1411657354293/3125000000000 : ℝ)^3405
        have hw : |(5428406599/10000000000 : ℝ)|=(5428406599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_9 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627758447/5000000000 : ℝ)*x 0 + (-37963891/200000000 : ℝ)*x 1 + (2714202739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627758447/5000000000 : ℝ)^4429 ≤ (135345855311/312500000000 : ℝ)^3405 := by
    have hnat : (2627758447 : ℕ)^4429*312500000000^3405 ≤ 135345855311^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627758447 5000000000 135345855311 312500000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37963891/200000000 : ℝ)^4429 ≤ (89971117867/781250000000 : ℝ)^3405 := by
    have hnat : (37963891 : ℕ)^4429*781250000000^3405 ≤ 89971117867^3405*200000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37963891 200000000 89971117867 781250000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714202739/5000000000 : ℝ)^4429 ≤ (22586511601729/50000000000000 : ℝ)^3405 := by
    have hnat : (2714202739 : ℕ)^4429*50000000000000^3405 ≤ 22586511601729^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714202739 5000000000 22586511601729 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627758447/5000000000 : ℝ), (-37963891/200000000 : ℝ), (2714202739/5000000000 : ℝ)] ![(135345855311/312500000000 : ℝ), (89971117867/781250000000 : ℝ), (22586511601729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627758447/5000000000 : ℝ)|^4429 ≤ (135345855311/312500000000 : ℝ)^3405
        have hw : |(2627758447/5000000000 : ℝ)|=(2627758447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37963891/200000000 : ℝ)|^4429 ≤ (89971117867/781250000000 : ℝ)^3405
        have hw : |(-37963891/200000000 : ℝ)|=(37963891/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714202739/5000000000 : ℝ)|^4429 ≤ (22586511601729/50000000000000 : ℝ)^3405
        have hw : |(2714202739/5000000000 : ℝ)|=(2714202739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_10 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131387909/250000000 : ℝ)*x 0 + (5428405599/10000000000 : ℝ)*x 1 + (-1898195109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131387909/250000000 : ℝ)^4429 ≤ (1353458374231/3125000000000 : ℝ)^3405 := by
    have hnat : (131387909 : ℕ)^4429*3125000000000^3405 ≤ 1353458374231^3405*250000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131387909 250000000 1353458374231 3125000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428405599/10000000000 : ℝ)^4429 ≤ (9034604902637/20000000000000 : ℝ)^3405 := by
    have hnat : (5428405599 : ℕ)^4429*20000000000000^3405 ≤ 9034604902637^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428405599 10000000000 9034604902637 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1898195109/10000000000 : ℝ)^4429 ≤ (11516307498339/100000000000000 : ℝ)^3405 := by
    have hnat : (1898195109 : ℕ)^4429*100000000000000^3405 ≤ 11516307498339^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898195109 10000000000 11516307498339 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131387909/250000000 : ℝ), (5428405599/10000000000 : ℝ), (-1898195109/10000000000 : ℝ)] ![(1353458374231/3125000000000 : ℝ), (9034604902637/20000000000000 : ℝ), (11516307498339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131387909/250000000 : ℝ)|^4429 ≤ (1353458374231/3125000000000 : ℝ)^3405
        have hw : |(131387909/250000000 : ℝ)|=(131387909/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428405599/10000000000 : ℝ)|^4429 ≤ (9034604902637/20000000000000 : ℝ)^3405
        have hw : |(5428405599/10000000000 : ℝ)|=(5428405599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1898195109/10000000000 : ℝ)|^4429 ≤ (11516307498339/100000000000000 : ℝ)^3405
        have hw : |(-1898195109/10000000000 : ℝ)|=(1898195109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_11 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4547052841/10000000000 : ℝ)*x 0 + (1042677389/2500000000 : ℝ)*x 1 + (4170710413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4547052841/10000000000 : ℝ)^4429 ≤ (35875478467919/100000000000000 : ℝ)^3405 := by
    have hnat : (4547052841 : ℕ)^4429*100000000000000^3405 ≤ 35875478467919^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547052841 10000000000 35875478467919 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042677389/2500000000 : ℝ)^4429 ≤ (16031128238663/50000000000000 : ℝ)^3405 := by
    have hnat : (1042677389 : ℕ)^4429*50000000000000^3405 ≤ 16031128238663^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042677389 2500000000 16031128238663 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170710413/10000000000 : ℝ)^4429 ≤ (32062265046787/100000000000000 : ℝ)^3405 := by
    have hnat : (4170710413 : ℕ)^4429*100000000000000^3405 ≤ 32062265046787^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170710413 10000000000 32062265046787 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4547052841/10000000000 : ℝ), (1042677389/2500000000 : ℝ), (4170710413/10000000000 : ℝ)] ![(35875478467919/100000000000000 : ℝ), (16031128238663/50000000000000 : ℝ), (32062265046787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4547052841/10000000000 : ℝ)|^4429 ≤ (35875478467919/100000000000000 : ℝ)^3405
        have hw : |(4547052841/10000000000 : ℝ)|=(4547052841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042677389/2500000000 : ℝ)|^4429 ≤ (16031128238663/50000000000000 : ℝ)^3405
        have hw : |(1042677389/2500000000 : ℝ)|=(1042677389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170710413/10000000000 : ℝ)|^4429 ≤ (32062265046787/100000000000000 : ℝ)^3405
        have hw : |(4170710413/10000000000 : ℝ)|=(4170710413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_12 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1810968263/10000000000 : ℝ)*x 0 + (137992451/250000000 : ℝ)*x 1 + (163338831/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1810968263/10000000000 : ℝ)^4429 ≤ (10832762924799/100000000000000 : ℝ)^3405 := by
    have hnat : (1810968263 : ℕ)^4429*100000000000000^3405 ≤ 10832762924799^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810968263 10000000000 10832762924799 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137992451/250000000 : ℝ)^4429 ≤ (9232736095711/20000000000000 : ℝ)^3405 := by
    have hnat : (137992451 : ℕ)^4429*20000000000000^3405 ≤ 9232736095711^3405*250000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137992451 250000000 9232736095711 20000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163338831/312500000 : ℝ)^4429 ≤ (43003556582711/100000000000000 : ℝ)^3405 := by
    have hnat : (163338831 : ℕ)^4429*100000000000000^3405 ≤ 43003556582711^3405*312500000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163338831 312500000 43003556582711 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1810968263/10000000000 : ℝ), (137992451/250000000 : ℝ), (163338831/312500000 : ℝ)] ![(10832762924799/100000000000000 : ℝ), (9232736095711/20000000000000 : ℝ), (43003556582711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1810968263/10000000000 : ℝ)|^4429 ≤ (10832762924799/100000000000000 : ℝ)^3405
        have hw : |(-1810968263/10000000000 : ℝ)|=(1810968263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137992451/250000000 : ℝ)|^4429 ≤ (9232736095711/20000000000000 : ℝ)^3405
        have hw : |(137992451/250000000 : ℝ)|=(137992451/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163338831/312500000 : ℝ)|^4429 ≤ (43003556582711/100000000000000 : ℝ)^3405
        have hw : |(163338831/312500000 : ℝ)|=(163338831/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_13 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698182279/5000000000 : ℝ)*x 0 + (-1980490237/10000000000 : ℝ)*x 1 + (5226842189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698182279/5000000000 : ℝ)^4429 ≤ (44826514407549/100000000000000 : ℝ)^3405 := by
    have hnat : (2698182279 : ℕ)^4429*100000000000000^3405 ≤ 44826514407549^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698182279 5000000000 44826514407549 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980490237/10000000000 : ℝ)^4429 ≤ (3042483325137/25000000000000 : ℝ)^3405 := by
    have hnat : (1980490237 : ℕ)^4429*25000000000000^3405 ≤ 3042483325137^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980490237 10000000000 3042483325137 25000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226842189/10000000000 : ℝ)^4429 ≤ (43003552269919/100000000000000 : ℝ)^3405 := by
    have hnat : (5226842189 : ℕ)^4429*100000000000000^3405 ≤ 43003552269919^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226842189 10000000000 43003552269919 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698182279/5000000000 : ℝ), (-1980490237/10000000000 : ℝ), (5226842189/10000000000 : ℝ)] ![(44826514407549/100000000000000 : ℝ), (3042483325137/25000000000000 : ℝ), (43003552269919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698182279/5000000000 : ℝ)|^4429 ≤ (44826514407549/100000000000000 : ℝ)^3405
        have hw : |(2698182279/5000000000 : ℝ)|=(2698182279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1980490237/10000000000 : ℝ)|^4429 ≤ (3042483325137/25000000000000 : ℝ)^3405
        have hw : |(-1980490237/10000000000 : ℝ)|=(1980490237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226842189/10000000000 : ℝ)|^4429 ≤ (43003552269919/100000000000000 : ℝ)^3405
        have hw : |(5226842189/10000000000 : ℝ)|=(5226842189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_14 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539636461/1000000000 : ℝ)*x 0 + (2613421221/5000000000 : ℝ)*x 1 + (-1980489829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539636461/1000000000 : ℝ)^4429 ≤ (22413257484703/50000000000000 : ℝ)^3405 := by
    have hnat : (539636461 : ℕ)^4429*50000000000000^3405 ≤ 22413257484703^3405*1000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539636461 1000000000 22413257484703 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613421221/5000000000 : ℝ)^4429 ≤ (43003554977453/100000000000000 : ℝ)^3405 := by
    have hnat : (2613421221 : ℕ)^4429*100000000000000^3405 ≤ 43003554977453^3405*5000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613421221 5000000000 43003554977453 100000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980489829/10000000000 : ℝ)^4429 ≤ (1521241254931/12500000000000 : ℝ)^3405 := by
    have hnat : (1980489829 : ℕ)^4429*12500000000000^3405 ≤ 1521241254931^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980489829 10000000000 1521241254931 12500000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539636461/1000000000 : ℝ), (2613421221/5000000000 : ℝ), (-1980489829/10000000000 : ℝ)] ![(22413257484703/50000000000000 : ℝ), (43003554977453/100000000000000 : ℝ), (1521241254931/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539636461/1000000000 : ℝ)|^4429 ≤ (22413257484703/50000000000000 : ℝ)^3405
        have hw : |(539636461/1000000000 : ℝ)|=(539636461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613421221/5000000000 : ℝ)|^4429 ≤ (43003554977453/100000000000000 : ℝ)^3405
        have hw : |(2613421221/5000000000 : ℝ)|=(2613421221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980489829/10000000000 : ℝ)|^4429 ≤ (1521241254931/12500000000000 : ℝ)^3405
        have hw : |(-1980489829/10000000000 : ℝ)|=(1980489829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1466_box_15 (p : ℝ) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1011517991/2500000000 : ℝ)*x 0 + (221059453/500000000 : ℝ)*x 1 + (4421188479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1011517991/2500000000 : ℝ)^4429 ≤ (15410799372293/50000000000000 : ℝ)^3405 := by
    have hnat : (1011517991 : ℕ)^4429*50000000000000^3405 ≤ 15410799372293^3405*2500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011517991 2500000000 15410799372293 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221059453/500000000 : ℝ)^4429 ≤ (17294601788783/50000000000000 : ℝ)^3405 := by
    have hnat : (221059453 : ℕ)^4429*50000000000000^3405 ≤ 17294601788783^3405*500000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221059453 500000000 17294601788783 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4421188479/10000000000 : ℝ)^4429 ≤ (17294598832567/50000000000000 : ℝ)^3405 := by
    have hnat : (4421188479 : ℕ)^4429*50000000000000^3405 ≤ 17294598832567^3405*10000000000^4429 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421188479 10000000000 17294598832567 50000000000000 4429 3405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4429/1024 : ℝ)) 4429 3405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1011517991/2500000000 : ℝ), (221059453/500000000 : ℝ), (4421188479/10000000000 : ℝ)] ![(15410799372293/50000000000000 : ℝ), (17294601788783/50000000000000 : ℝ), (17294598832567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1011517991/2500000000 : ℝ)|^4429 ≤ (15410799372293/50000000000000 : ℝ)^3405
        have hw : |(1011517991/2500000000 : ℝ)|=(1011517991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221059453/500000000 : ℝ)|^4429 ≤ (17294601788783/50000000000000 : ℝ)^3405
        have hw : |(221059453/500000000 : ℝ)|=(221059453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4421188479/10000000000 : ℝ)|^4429 ≤ (17294598832567/50000000000000 : ℝ)^3405
        have hw : |(4421188479/10000000000 : ℝ)|=(4421188479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1466_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15471/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63689/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58413/100000 : ℝ) ∧ (79809/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85701/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15471/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (429/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15471/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (429/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15471/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (429/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15471/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (429/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15471/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (429/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15471/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (429/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (429/4000 : ℝ) ^ (4427/1024 : ℝ) ≤ (401839591162521/6250000000000000000 : ℝ) := by
    have hpowers : (429/4000 : ℝ)^4427 ≤ (401839591162521/6250000000000000000 : ℝ)^1024 := by
      have hnat : (429 : ℕ)^4427*6250000000000000000^1024 ≤ 401839591162521^1024*4000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        429 4000 401839591162521 6250000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (429/4000 : ℝ)) (X := (401839591162521/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15471/100000 : ℝ) ^ (4427/1024 : ℝ) ≤ (15669736700143013/50000000000000000000 : ℝ) := by
    have hpowers : (15471/100000 : ℝ)^4427 ≤ (15669736700143013/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15471 : ℕ)^4427*50000000000000000000^1024 ≤ 15669736700143013^1024*100000^4427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15471 100000 15669736700143013 50000000000000000000 4427 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15471/100000 : ℝ)) (X := (15669736700143013/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125401839591162521/3125000000000000000 : ℝ) ≤ (2500074355257523/2500000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (3125401839591162521/3125000000000000000 : ℝ)^1024 ≤ (2500074355257523/2500000000000000 : ℝ)^4427 := by
      have hnat : (3125401839591162521 : ℕ)^1024*2500000000000000^4427 ≤ 2500074355257523^4427*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125401839591162521 3125000000000000000 2500074355257523 2500000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500074355257523/2500000000000000 : ℝ)) (X := (3125401839591162521/3125000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018884453429443181/50000000000000000000 : ℝ) ≤ (5000436748900273/5000000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (50018884453429443181/50000000000000000000 : ℝ)^1024 ≤ (5000436748900273/5000000000000000 : ℝ)^4427 := by
      have hnat : (50018884453429443181 : ℕ)^1024*5000000000000000^4427 ≤ 5000436748900273^4427*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018884453429443181 50000000000000000000 5000436748900273 5000000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000436748900273/5000000000000000 : ℝ)) (X := (50018884453429443181/50000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015669736700143013/25000000000000000000 : ℝ) ≤ (10001449574571/10000000000000 : ℝ) ^ (4427/1024 : ℝ) := by
    have hpowers : (25015669736700143013/25000000000000000000 : ℝ)^1024 ≤ (10001449574571/10000000000000 : ℝ)^4427 := by
      have hnat : (25015669736700143013 : ℕ)^1024*10000000000000^4427 ≤ 10001449574571^4427*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015669736700143013 25000000000000000000 10001449574571 10000000000000 1024 4427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001449574571/10000000000000 : ℝ)) (X := (25015669736700143013/25000000000000000000 : ℝ)) (by norm_num) 4427 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(401839591162521/6250000000000000000 : ℝ) ≤ ((3954087892790214861/3955000000000000000 : ℝ)+2*(288038385227/237300000000000 : ℝ)*(429/4000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (3954087892790214861/3955000000000000000 : ℝ)+2*(288038385227/237300000000000 : ℝ)*(429/4000 : ℝ)=(2500074355257523/2500000000000000 : ℝ) by norm_num, show 1+2*(401839591162521/6250000000000000000 : ℝ)=(3125401839591162521/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15669736700143013/50000000000000000000 : ℝ)+(401839591162521/6250000000000000000 : ℝ) ≤ ((3954087892790214861/3955000000000000000 : ℝ)+(288038385227/237300000000000 : ℝ)*((15471/100000 : ℝ)+(429/4000 : ℝ)))^(4427/1024 : ℝ) := by
    rw [show (3954087892790214861/3955000000000000000 : ℝ)+(288038385227/237300000000000 : ℝ)*((15471/100000 : ℝ)+(429/4000 : ℝ))=(5000436748900273/5000000000000000 : ℝ) by norm_num, show 1+(15669736700143013/50000000000000000000 : ℝ)+(401839591162521/6250000000000000000 : ℝ)=(50018884453429443181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15669736700143013/50000000000000000000 : ℝ) ≤ ((3954087892790214861/3955000000000000000 : ℝ)+2*(288038385227/237300000000000 : ℝ)*(15471/100000 : ℝ))^(4427/1024 : ℝ) := by
    rw [show (3954087892790214861/3955000000000000000 : ℝ)+2*(288038385227/237300000000000 : ℝ)*(15471/100000 : ℝ)=(10001449574571/10000000000000 : ℝ) by norm_num, show 1+2*(15669736700143013/50000000000000000000 : ℝ)=(25015669736700143013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3954087892790214861/3955000000000000000 : ℝ)*(X 1 0+X 2 0)+(288038385227/237300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (15471/100000 : ℝ)) (c := (3954087892790214861/3955000000000000000 : ℝ)) (alpha := (288038385227/237300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3954087892790214861/3955000000000000000 : ℝ)*(X 0 1+X 2 1)+(288038385227/237300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (15471/100000 : ℝ)) (c := (3954087892790214861/3955000000000000000 : ℝ)) (alpha := (288038385227/237300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3954087892790214861/3955000000000000000 : ℝ)*(X 0 2+X 1 2)+(288038385227/237300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4427/1024 : ℝ)) (lo := (429/4000 : ℝ)) (hi := (15471/100000 : ℝ)) (c := (3954087892790214861/3955000000000000000 : ℝ)) (alpha := (288038385227/237300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1715939313/10000000000 : ℝ)*X 0 0+(5407822913/10000000000 : ℝ)*X 0 1+(337988917/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1053981459/2000000000 : ℝ)*X 1 0+(-1906849441/10000000000 : ℝ)*X 1 1+(2703911287/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1317476747/2500000000 : ℝ)*X 2 0+(2703911521/5000000000 : ℝ)*X 2 1+(-1906849217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1124255083/2500000000 : ℝ)*X 0 0+(26226989/62500000 : ℝ)*X 0 1+(65567481/156250000 : ℝ)*X 0 2+(1124255083/2500000000 : ℝ)*X 1 0+(26226989/62500000 : ℝ)*X 1 1+(65567481/156250000 : ℝ)*X 1 2+(1124255083/2500000000 : ℝ)*X 2 0+(26226989/62500000 : ℝ)*X 2 1+(65567481/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86635867/400000000 : ℝ)*X 0 0+(209672587/400000000 : ℝ)*X 0 1+(5241815101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692952239/5000000000 : ℝ)*X 1 0+(-1974568017/10000000000 : ℝ)*X 1 1+(5241814829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1346476151/2500000000 : ℝ)*X 2 0+(1048362981/2000000000 : ℝ)*X 2 1+(-1974567743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4084165957/10000000000 : ℝ)*X 0 0+(2201302373/5000000000 : ℝ)*X 0 1+(2201302597/5000000000 : ℝ)*X 0 2+(4084165957/10000000000 : ℝ)*X 1 0+(2201302373/5000000000 : ℝ)*X 1 1+(2201302597/5000000000 : ℝ)*X 1 2+(4084165957/10000000000 : ℝ)*X 2 0+(2201302373/5000000000 : ℝ)*X 2 1+(2201302597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-414216967/2000000000 : ℝ)*X 0 0+(5126044851/10000000000 : ℝ)*X 0 1+(5428406599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2627758447/5000000000 : ℝ)*X 1 0+(-37963891/200000000 : ℝ)*X 1 1+(2714202739/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((131387909/250000000 : ℝ)*X 2 0+(5428405599/10000000000 : ℝ)*X 2 1+(-1898195109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4547052841/10000000000 : ℝ)*X 0 0+(1042677389/2500000000 : ℝ)*X 0 1+(4170710413/10000000000 : ℝ)*X 0 2+(4547052841/10000000000 : ℝ)*X 1 0+(1042677389/2500000000 : ℝ)*X 1 1+(4170710413/10000000000 : ℝ)*X 1 2+(4547052841/10000000000 : ℝ)*X 2 0+(1042677389/2500000000 : ℝ)*X 2 1+(4170710413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1810968263/10000000000 : ℝ)*X 0 0+(137992451/250000000 : ℝ)*X 0 1+(163338831/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2698182279/5000000000 : ℝ)*X 1 0+(-1980490237/10000000000 : ℝ)*X 1 1+(5226842189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((539636461/1000000000 : ℝ)*X 2 0+(2613421221/5000000000 : ℝ)*X 2 1+(-1980489829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1011517991/2500000000 : ℝ)*X 0 0+(221059453/500000000 : ℝ)*X 0 1+(4421188479/10000000000 : ℝ)*X 0 2+(1011517991/2500000000 : ℝ)*X 1 0+(221059453/500000000 : ℝ)*X 1 1+(4421188479/10000000000 : ℝ)*X 1 2+(1011517991/2500000000 : ℝ)*X 2 0+(221059453/500000000 : ℝ)*X 2 1+(4421188479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1466_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63689/100000 : ℝ) ≤ (-8995691733104358391520024338939/14125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13244893/100000000000000 : ℝ)*(lower0) + (954861/625000000000 : ℝ)*(lower2) + (167764407/100000000000000 : ℝ)*(lower3) + (1096889/800000000000 : ℝ)*(lower4) + (2154565980328531/100000000000000 : ℝ)*(major0) + (2154565980328531/100000000000000 : ℝ)*(major1) + (2154565980328531/100000000000000 : ℝ)*(major2) + (1490673275084853/50000000000000 : ℝ)*(sp4) + (186330541462331/6250000000000 : ℝ)*(sp5) + (46582962473157/1562500000000 : ℝ)*(sp6) + (1348977137590081/100000000000000 : ℝ)*(sp7) + (57886772409/100000000000000 : ℝ)*(sp13) + (36951887657/100000000000000 : ℝ)*(sp14) + (926098721/2500000000000 : ℝ)*(sp15) + (674507090769461/50000000000000 : ℝ)*(f.failure) + (1490673275084853/50000000000000 : ℝ)*(f.sum) + (4828290878263/847500000000000000000000000 : ℝ)*base65 + (460613600289763939/169500000000000000000000000000000 : ℝ)*base67 + (36593462888236061/169500000000000000000000000000000 : ℝ)*base70 + (2810270804225263939/169500000000000000000000000000000 : ℝ)*base71 + (208444001099/423750000000000000000000000 : ℝ)*base73 + (121018590371263939/169500000000000000000000000000000 : ℝ)*base75 + (846613973411263939/169500000000000000000000000000000 : ℝ)*base77 + (363553106151763939/169500000000000000000000000000000 : ℝ)*base79 + (2504527063919/423750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (38025249/5000000000000000000000 : ℝ)*base89 + (38025249/5000000000000000000000 : ℝ)*base91 + (38025249/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58413/100000 : ℝ) ≤ (902467067933818498156012366387/1544921875000000000000000000000 : ℝ) := by norm_num
    linear_combination (58399169/100000000000000 : ℝ)*(lower0) + (138784997/100000000000000 : ℝ)*(lower1) + (5078963/50000000000000 : ℝ)*(lower2) + (20520543/100000000000000 : ℝ)*(lower3) + (4792173/25000000000000 : ℝ)*(lower5) + (2227699034345797/100000000000000 : ℝ)*(major0) + (2227699034345797/100000000000000 : ℝ)*(major1) + (1113849517172899/50000000000000 : ℝ)*(major2) + (304112222273783/10000000000000 : ℝ)*(sp0) + (3041050285633659/100000000000000 : ℝ)*(sp1) + (304112222273783/10000000000000 : ℝ)*(sp2) + (697400776938157/50000000000000 : ℝ)*(sp3) + (1302406567/50000000000000 : ℝ)*(sp7) + (71937104171/100000000000000 : ℝ)*(sp9) + (174350519836181/12500000000000 : ℝ)*(f.failure) + (304112222273783/10000000000000 : ℝ)*(f.sum) + (2548803615399/1582000000000000000000000000 : ℝ)*base65 + (9459383182346832349/1186500000000000000000000000000000 : ℝ)*base68 + (5184789200147268883/593250000000000000000000000000000 : ℝ)*base70 + (10792300427758332349/1186500000000000000000000000000000 : ℝ)*base72 + (2914022667739/1582000000000000000000000000 : ℝ)*base74 + (59930996150268883/593250000000000000000000000000000 : ℝ)*base76 + (2998285051946182349/1186500000000000000000000000000000 : ℝ)*base78 + (5597703254663182349/1186500000000000000000000000000000 : ℝ)*base80 + (77795804059711/11865000000000000000000000000 : ℝ)*base82 + (11877729/1250000000000000000000 : ℝ)*base89 + (11877729/1250000000000000000000 : ℝ)*base91 + (622271/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79809/100000 : ℝ) ≤ (99764922883864406260335045811/125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138197617/100000000000000 : ℝ)*(upper0) + (176610227/100000000000000 : ℝ)*(upper2) + (137677/250000000000 : ℝ)*(lower3) + (247939401/100000000000000 : ℝ)*(lower5) + (1213318707798253/50000000000000 : ℝ)*(major0) + (1213318707798253/50000000000000 : ℝ)*(major1) + (1213318707798253/50000000000000 : ℝ)*(major2) + (61150662999/100000000000000 : ℝ)*(sp3) + (9217303639/100000000000000 : ℝ)*(sp4) + (165364564710619/5000000000000 : ℝ)*(sp8) + (1653653820167631/50000000000000 : ℝ)*(sp9) + (1653653820167631/50000000000000 : ℝ)*(sp10) + (759651030379523/50000000000000 : ℝ)*(sp11) + (7128819243/100000000000000 : ℝ)*(sp12) + (303872642284409/20000000000000 : ℝ)*(f.failure) + (1653653820167631/50000000000000 : ℝ)*(f.sum) + (7973630982683/847500000000000000000000000 : ℝ)*base65 + (1067483096541373357/84750000000000000000000000000000 : ℝ)*base67 + (241426671378373357/84750000000000000000000000000000 : ℝ)*base69 + (822419538376643/84750000000000000000000000000000 : ℝ)*base72 + (3781200680123/847500000000000000000000000 : ℝ)*base73 + (198727992398623357/84750000000000000000000000000000 : ℝ)*base75 + (841510365164623357/84750000000000000000000000000000 : ℝ)*base77 + (283092099435376643/84750000000000000000000000000000 : ℝ)*base80 + (2862712029173/847500000000000000000000000 : ℝ)*base81 + (11973419/2000000000000000000000 : ℝ)*base90 + (11973419/2000000000000000000000 : ℝ)*base92 + (11973419/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85701/100000 : ℝ) ≤ (-756556070709087001437335223789/882812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3222019/100000000000000 : ℝ)*(lower0) + (73658729/50000000000000 : ℝ)*(lower2) + (10233903/50000000000000 : ℝ)*(upper3) + (308077020652737/12500000000000 : ℝ)*(major0) + (308077020652737/12500000000000 : ℝ)*(major1) + (308077020652737/12500000000000 : ℝ)*(major2) + (2463049009/50000000000000 : ℝ)*(sp0) + (41280463043/25000000000000 : ℝ)*(sp5) + (2578722959/6250000000000 : ℝ)*(sp6) + (8033034657/25000000000000 : ℝ)*(sp7) + (1707325557098647/50000000000000 : ℝ)*(sp12) + (170724545922157/5000000000000 : ℝ)*(sp13) + (106706711897749/3125000000000 : ℝ)*(sp14) + (12344882295467/800000000000 : ℝ)*(sp15) + (1543142419072003/100000000000000 : ℝ)*(f.failure) + (213416002518457/6250000000000 : ℝ)*(f.sum) + (589386190813/141250000000000000000000000 : ℝ)*base65 + (42698463174535651/7062500000000000000000000000000 : ℝ)*base67 + (46027967409651849/7062500000000000000000000000000 : ℝ)*base70 + (28200226646410651/7062500000000000000000000000000 : ℝ)*base71 + (165619826527/141250000000000000000000000 : ℝ)*base74 + (16968954143348151/7062500000000000000000000000000 : ℝ)*base75 + (59366997336410651/7062500000000000000000000000000 : ℝ)*base77 + (34647990176660651/7062500000000000000000000000000 : ℝ)*base79 + (2749702028693/565000000000000000000000000 : ℝ)*base82 + (34009673/10000000000000000000000 : ℝ)*base90 + (34009673/10000000000000000000000 : ℝ)*base92 + (34009673/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1466_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15471/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (429/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63689/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58413/100000 : ℝ) else (79809/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85701/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1466_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1466_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63689/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58413/100000 : ℝ) else (79809/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85701/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1466_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1466_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1466_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4427/1024 : ℝ) ≤ p) (hpb : p ≤ (4429/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159714109/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63689/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58413/100000 : ℝ) else (79809/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85701/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1466_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
