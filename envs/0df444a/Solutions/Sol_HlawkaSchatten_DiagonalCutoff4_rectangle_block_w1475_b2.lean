-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1475_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:44.905178+00:00
-- url     : https://prove2.me/submissions/963032b4-f373-49ba-a080-85dc31caef2a

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
theorem support_rectangle_w1475_s6_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1924094521/10000000000 : ℝ)*x 0 + (679761319/1250000000 : ℝ)*x 1 + (2607768603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1924094521/10000000000 : ℝ)^4447 ≤ (5875850516963/50000000000000 : ℝ)^3423 := by
    have hnat : (1924094521 : ℕ)^4447*50000000000000^3423 ≤ 5875850516963^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924094521 10000000000 5875850516963 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679761319/1250000000 : ℝ)^4447 ≤ (45321523233757/100000000000000 : ℝ)^3423 := by
    have hnat : (679761319 : ℕ)^4447*100000000000000^3423 ≤ 45321523233757^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679761319 1250000000 45321523233757 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607768603/5000000000 : ℝ)^4447 ≤ (10731693929443/25000000000000 : ℝ)^3423 := by
    have hnat : (2607768603 : ℕ)^4447*25000000000000^3423 ≤ 10731693929443^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607768603 5000000000 10731693929443 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1924094521/10000000000 : ℝ), (679761319/1250000000 : ℝ), (2607768603/5000000000 : ℝ)] ![(5875850516963/50000000000000 : ℝ), (45321523233757/100000000000000 : ℝ), (10731693929443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1924094521/10000000000 : ℝ)|^4447 ≤ (5875850516963/50000000000000 : ℝ)^3423
        have hw : |(-1924094521/10000000000 : ℝ)|=(1924094521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679761319/1250000000 : ℝ)|^4447 ≤ (45321523233757/100000000000000 : ℝ)^3423
        have hw : |(679761319/1250000000 : ℝ)|=(679761319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607768603/5000000000 : ℝ)|^4447 ≤ (10731693929443/25000000000000 : ℝ)^3423
        have hw : |(2607768603/5000000000 : ℝ)|=(2607768603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338391399/2500000000 : ℝ)*x 0 + (-127385283/625000000 : ℝ)*x 1 + (1043107443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338391399/2500000000 : ℝ)^4447 ≤ (44408485583127/100000000000000 : ℝ)^3423 := by
    have hnat : (1338391399 : ℕ)^4447*100000000000000^3423 ≤ 44408485583127^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338391399 2500000000 44408485583127 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127385283/625000000 : ℝ)^4447 ≤ (6332369294841/50000000000000 : ℝ)^3423 := by
    have hnat : (127385283 : ℕ)^4447*50000000000000^3423 ≤ 6332369294841^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127385283 625000000 6332369294841 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043107443/2000000000 : ℝ)^4447 ≤ (21463387907003/50000000000000 : ℝ)^3423 := by
    have hnat : (1043107443 : ℕ)^4447*50000000000000^3423 ≤ 21463387907003^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043107443 2000000000 21463387907003 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338391399/2500000000 : ℝ), (-127385283/625000000 : ℝ), (1043107443/2000000000 : ℝ)] ![(44408485583127/100000000000000 : ℝ), (6332369294841/50000000000000 : ℝ), (21463387907003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338391399/2500000000 : ℝ)|^4447 ≤ (44408485583127/100000000000000 : ℝ)^3423
        have hw : |(1338391399/2500000000 : ℝ)|=(1338391399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127385283/625000000 : ℝ)|^4447 ≤ (6332369294841/50000000000000 : ℝ)^3423
        have hw : |(-127385283/625000000 : ℝ)|=(127385283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043107443/2000000000 : ℝ)|^4447 ≤ (21463387907003/50000000000000 : ℝ)^3423
        have hw : |(1043107443/2000000000 : ℝ)|=(1043107443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353565589/10000000000 : ℝ)*x 0 + (2607768607/5000000000 : ℝ)*x 1 + (-2038164539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353565589/10000000000 : ℝ)^4447 ≤ (44408485507691/100000000000000 : ℝ)^3423 := by
    have hnat : (5353565589 : ℕ)^4447*100000000000000^3423 ≤ 44408485507691^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353565589 10000000000 44408485507691 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607768607/5000000000 : ℝ)^4447 ≤ (21463387901657/50000000000000 : ℝ)^3423 := by
    have hnat : (2607768607 : ℕ)^4447*50000000000000^3423 ≤ 21463387901657^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607768607 5000000000 21463387901657 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038164539/10000000000 : ℝ)^4447 ≤ (6332369339241/50000000000000 : ℝ)^3423 := by
    have hnat : (2038164539 : ℕ)^4447*50000000000000^3423 ≤ 6332369339241^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038164539 10000000000 6332369339241 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353565589/10000000000 : ℝ), (2607768607/5000000000 : ℝ), (-2038164539/10000000000 : ℝ)] ![(44408485507691/100000000000000 : ℝ), (21463387901657/50000000000000 : ℝ), (6332369339241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353565589/10000000000 : ℝ)|^4447 ≤ (44408485507691/100000000000000 : ℝ)^3423
        have hw : |(5353565589/10000000000 : ℝ)|=(5353565589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607768607/5000000000 : ℝ)|^4447 ≤ (21463387901657/50000000000000 : ℝ)^3423
        have hw : |(2607768607/5000000000 : ℝ)|=(2607768607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038164539/10000000000 : ℝ)|^4447 ≤ (6332369339241/50000000000000 : ℝ)^3423
        have hw : |(-2038164539/10000000000 : ℝ)|=(2038164539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287319501/10000000000 : ℝ)*x 0 + (4047724141/10000000000 : ℝ)*x 1 + (2269626811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287319501/10000000000 : ℝ)^4447 ≤ (33277693698367/100000000000000 : ℝ)^3423 := by
    have hnat : (4287319501 : ℕ)^4447*100000000000000^3423 ≤ 33277693698367^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287319501 10000000000 33277693698367 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4047724141/10000000000 : ℝ)^4447 ≤ (30882109171931/100000000000000 : ℝ)^3423 := by
    have hnat : (4047724141 : ℕ)^4447*100000000000000^3423 ≤ 30882109171931^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047724141 10000000000 30882109171931 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269626811/5000000000 : ℝ)^4447 ≤ (17920098561543/50000000000000 : ℝ)^3423 := by
    have hnat : (2269626811 : ℕ)^4447*50000000000000^3423 ≤ 17920098561543^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269626811 5000000000 17920098561543 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287319501/10000000000 : ℝ), (4047724141/10000000000 : ℝ), (2269626811/5000000000 : ℝ)] ![(33277693698367/100000000000000 : ℝ), (30882109171931/100000000000000 : ℝ), (17920098561543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287319501/10000000000 : ℝ)|^4447 ≤ (33277693698367/100000000000000 : ℝ)^3423
        have hw : |(4287319501/10000000000 : ℝ)|=(4287319501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4047724141/10000000000 : ℝ)|^4447 ≤ (30882109171931/100000000000000 : ℝ)^3423
        have hw : |(4047724141/10000000000 : ℝ)|=(4047724141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269626811/5000000000 : ℝ)|^4447 ≤ (17920098561543/50000000000000 : ℝ)^3423
        have hw : |(2269626811/5000000000 : ℝ)|=(2269626811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-962062551/5000000000 : ℝ)*x 0 + (5216674657/10000000000 : ℝ)*x 1 + (5436944747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962062551/5000000000 : ℝ)^4447 ≤ (5875971843913/50000000000000 : ℝ)^3423 := by
    have hnat : (962062551 : ℕ)^4447*50000000000000^3423 ≤ 5875971843913^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962062551 5000000000 5875971843913 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216674657/10000000000 : ℝ)^4447 ≤ (42938938594769/100000000000000 : ℝ)^3423 := by
    have hnat : (5216674657 : ℕ)^4447*100000000000000^3423 ≤ 42938938594769^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216674657 10000000000 42938938594769 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436944747/10000000000 : ℝ)^4447 ≤ (45309117703901/100000000000000 : ℝ)^3423 := by
    have hnat : (5436944747 : ℕ)^4447*100000000000000^3423 ≤ 45309117703901^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436944747 10000000000 45309117703901 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962062551/5000000000 : ℝ), (5216674657/10000000000 : ℝ), (5436944747/10000000000 : ℝ)] ![(5875971843913/50000000000000 : ℝ), (42938938594769/100000000000000 : ℝ), (45309117703901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962062551/5000000000 : ℝ)|^4447 ≤ (5875971843913/50000000000000 : ℝ)^3423
        have hw : |(-962062551/5000000000 : ℝ)|=(962062551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216674657/10000000000 : ℝ)|^4447 ≤ (42938938594769/100000000000000 : ℝ)^3423
        have hw : |(5216674657/10000000000 : ℝ)|=(5216674657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436944747/10000000000 : ℝ)|^4447 ≤ (45309117703901/100000000000000 : ℝ)^3423
        have hw : |(5436944747/10000000000 : ℝ)|=(5436944747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647746589/5000000000 : ℝ)*x 0 + (-113547313/625000000 : ℝ)*x 1 + (1087388949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647746589/5000000000 : ℝ)^4447 ≤ (43783678485701/100000000000000 : ℝ)^3423 := by
    have hnat : (2647746589 : ℕ)^4447*100000000000000^3423 ≤ 43783678485701^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647746589 5000000000 43783678485701 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113547313/625000000 : ℝ)^4447 ≤ (10907203814101/100000000000000 : ℝ)^3423 := by
    have hnat : (113547313 : ℕ)^4447*100000000000000^3423 ≤ 10907203814101^3423*625000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113547313 625000000 10907203814101 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087388949/2000000000 : ℝ)^4447 ≤ (45309117682247/100000000000000 : ℝ)^3423 := by
    have hnat : (1087388949 : ℕ)^4447*100000000000000^3423 ≤ 45309117682247^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087388949 2000000000 45309117682247 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647746589/5000000000 : ℝ), (-113547313/625000000 : ℝ), (1087388949/2000000000 : ℝ)] ![(43783678485701/100000000000000 : ℝ), (10907203814101/100000000000000 : ℝ), (45309117682247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647746589/5000000000 : ℝ)|^4447 ≤ (43783678485701/100000000000000 : ℝ)^3423
        have hw : |(2647746589/5000000000 : ℝ)|=(2647746589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113547313/625000000 : ℝ)|^4447 ≤ (10907203814101/100000000000000 : ℝ)^3423
        have hw : |(-113547313/625000000 : ℝ)|=(113547313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1087388949/2000000000 : ℝ)|^4447 ≤ (45309117682247/100000000000000 : ℝ)^3423
        have hw : |(1087388949/2000000000 : ℝ)|=(1087388949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295493181/10000000000 : ℝ)*x 0 + (2718472373/5000000000 : ℝ)*x 1 + (-1816757003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295493181/10000000000 : ℝ)^4447 ≤ (21891839258963/50000000000000 : ℝ)^3423 := by
    have hnat : (5295493181 : ℕ)^4447*50000000000000^3423 ≤ 21891839258963^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295493181 10000000000 21891839258963 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718472373/5000000000 : ℝ)^4447 ≤ (22654558846537/50000000000000 : ℝ)^3423 := by
    have hnat : (2718472373 : ℕ)^4447*50000000000000^3423 ≤ 22654558846537^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718472373 5000000000 22654558846537 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1816757003/10000000000 : ℝ)^4447 ≤ (5453601887551/50000000000000 : ℝ)^3423 := by
    have hnat : (1816757003 : ℕ)^4447*50000000000000^3423 ≤ 5453601887551^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1816757003 10000000000 5453601887551 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295493181/10000000000 : ℝ), (2718472373/5000000000 : ℝ), (-1816757003/10000000000 : ℝ)] ![(21891839258963/50000000000000 : ℝ), (22654558846537/50000000000000 : ℝ), (5453601887551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295493181/10000000000 : ℝ)|^4447 ≤ (21891839258963/50000000000000 : ℝ)^3423
        have hw : |(5295493181/10000000000 : ℝ)|=(5295493181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718472373/5000000000 : ℝ)|^4447 ≤ (22654558846537/50000000000000 : ℝ)^3423
        have hw : |(2718472373/5000000000 : ℝ)|=(2718472373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1816757003/10000000000 : ℝ)|^4447 ≤ (5453601887551/50000000000000 : ℝ)^3423
        have hw : |(-1816757003/10000000000 : ℝ)|=(1816757003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_s6_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287387053/10000000000 : ℝ)*x 0 + (453674151/1000000000 : ℝ)*x 1 + (4050254699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287387053/10000000000 : ℝ)^4447 ≤ (2079898430383/6250000000000 : ℝ)^3423 := by
    have hnat : (4287387053 : ℕ)^4447*6250000000000^3423 ≤ 2079898430383^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287387053 10000000000 2079898430383 6250000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453674151/1000000000 : ℝ)^4447 ≤ (17907215495973/50000000000000 : ℝ)^3423 := by
    have hnat : (453674151 : ℕ)^4447*50000000000000^3423 ≤ 17907215495973^3423*1000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453674151 1000000000 17907215495973 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4050254699/10000000000 : ℝ)^4447 ≤ (30907194118309/100000000000000 : ℝ)^3423 := by
    have hnat : (4050254699 : ℕ)^4447*100000000000000^3423 ≤ 30907194118309^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050254699 10000000000 30907194118309 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287387053/10000000000 : ℝ), (453674151/1000000000 : ℝ), (4050254699/10000000000 : ℝ)] ![(2079898430383/6250000000000 : ℝ), (17907215495973/50000000000000 : ℝ), (30907194118309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287387053/10000000000 : ℝ)|^4447 ≤ (2079898430383/6250000000000 : ℝ)^3423
        have hw : |(4287387053/10000000000 : ℝ)|=(4287387053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453674151/1000000000 : ℝ)|^4447 ≤ (17907215495973/50000000000000 : ℝ)^3423
        have hw : |(453674151/1000000000 : ℝ)|=(453674151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4050254699/10000000000 : ℝ)|^4447 ≤ (30907194118309/100000000000000 : ℝ)^3423
        have hw : |(4050254699/10000000000 : ℝ)|=(4050254699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2153/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10763/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10763/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10763/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10763/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10763/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10763/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10763/100000 : ℝ) ^ (4445/1024 : ℝ) ≤ (3138821248587979/50000000000000000000 : ℝ) := by
    have hpowers : (10763/100000 : ℝ)^4445 ≤ (3138821248587979/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10763 : ℕ)^4445*50000000000000000000^1024 ≤ 3138821248587979^1024*100000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10763 100000 3138821248587979 50000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10763/100000 : ℝ)) (X := (3138821248587979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4445/1024 : ℝ) ≤ (3796331506820331/12500000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4445 ≤ (3796331506820331/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4445*12500000000000000000^1024 ≤ 3796331506820331^1024*25000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 3796331506820331 12500000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (3796331506820331/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003138821248587979/25000000000000000000 : ℝ) ≤ (500014461181911/500000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (25003138821248587979/25000000000000000000 : ℝ)^1024 ≤ (500014461181911/500000000000000 : ℝ)^4445 := by
      have hnat : (25003138821248587979 : ℕ)^1024*500000000000000^4445 ≤ 500014461181911^4445*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003138821248587979 25000000000000000000 500014461181911 500000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014461181911/500000000000000 : ℝ)) (X := (25003138821248587979/25000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018324147275869303/50000000000000000000 : ℝ) ≤ (10000844152132507/10000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (50018324147275869303/50000000000000000000 : ℝ)^1024 ≤ (10000844152132507/10000000000000000 : ℝ)^4445 := by
      have hnat : (50018324147275869303 : ℕ)^1024*10000000000000000^4445 ≤ 10000844152132507^4445*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018324147275869303 50000000000000000000 10000844152132507 10000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000844152132507/10000000000000000 : ℝ)) (X := (50018324147275869303/50000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253796331506820331/6250000000000000000 : ℝ) ≤ (5000699540313397/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (6253796331506820331/6250000000000000000 : ℝ)^1024 ≤ (5000699540313397/5000000000000000 : ℝ)^4445 := by
      have hnat : (6253796331506820331 : ℕ)^1024*5000000000000000^4445 ≤ 5000699540313397^4445*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253796331506820331 6250000000000000000 5000699540313397 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000699540313397/5000000000000000 : ℝ)) (X := (6253796331506820331/6250000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3138821248587979/50000000000000000000 : ℝ) ≤ ((23559708860119454449/23565000000000000000 : ℝ)+2*(554928494287/471300000000000 : ℝ)*(10763/100000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (23559708860119454449/23565000000000000000 : ℝ)+2*(554928494287/471300000000000 : ℝ)*(10763/100000 : ℝ)=(500014461181911/500000000000000 : ℝ) by norm_num, show 1+2*(3138821248587979/50000000000000000000 : ℝ)=(25003138821248587979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3796331506820331/12500000000000000000 : ℝ)+(3138821248587979/50000000000000000000 : ℝ) ≤ ((23559708860119454449/23565000000000000000 : ℝ)+(554928494287/471300000000000 : ℝ)*((3869/25000 : ℝ)+(10763/100000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (23559708860119454449/23565000000000000000 : ℝ)+(554928494287/471300000000000 : ℝ)*((3869/25000 : ℝ)+(10763/100000 : ℝ))=(10000844152132507/10000000000000000 : ℝ) by norm_num, show 1+(3796331506820331/12500000000000000000 : ℝ)+(3138821248587979/50000000000000000000 : ℝ)=(50018324147275869303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3796331506820331/12500000000000000000 : ℝ) ≤ ((23559708860119454449/23565000000000000000 : ℝ)+2*(554928494287/471300000000000 : ℝ)*(3869/25000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (23559708860119454449/23565000000000000000 : ℝ)+2*(554928494287/471300000000000 : ℝ)*(3869/25000 : ℝ)=(5000699540313397/5000000000000000 : ℝ) by norm_num, show 1+2*(3796331506820331/12500000000000000000 : ℝ)=(6253796331506820331/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23559708860119454449/23565000000000000000 : ℝ)*(X 1 0+X 2 0)+(554928494287/471300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10763/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (23559708860119454449/23565000000000000000 : ℝ)) (alpha := (554928494287/471300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23559708860119454449/23565000000000000000 : ℝ)*(X 0 1+X 2 1)+(554928494287/471300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10763/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (23559708860119454449/23565000000000000000 : ℝ)) (alpha := (554928494287/471300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23559708860119454449/23565000000000000000 : ℝ)*(X 0 2+X 1 2)+(554928494287/471300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (10763/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (23559708860119454449/23565000000000000000 : ℝ)) (alpha := (554928494287/471300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1924094521/10000000000 : ℝ)*X 0 0+(679761319/1250000000 : ℝ)*X 0 1+(2607768603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338391399/2500000000 : ℝ)*X 1 0+(-127385283/625000000 : ℝ)*X 1 1+(1043107443/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353565589/10000000000 : ℝ)*X 2 0+(2607768607/5000000000 : ℝ)*X 2 1+(-2038164539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4287319501/10000000000 : ℝ)*X 0 0+(4047724141/10000000000 : ℝ)*X 0 1+(2269626811/5000000000 : ℝ)*X 0 2+(4287319501/10000000000 : ℝ)*X 1 0+(4047724141/10000000000 : ℝ)*X 1 1+(2269626811/5000000000 : ℝ)*X 1 2+(4287319501/10000000000 : ℝ)*X 2 0+(4047724141/10000000000 : ℝ)*X 2 1+(2269626811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-962062551/5000000000 : ℝ)*X 0 0+(5216674657/10000000000 : ℝ)*X 0 1+(5436944747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647746589/5000000000 : ℝ)*X 1 0+(-113547313/625000000 : ℝ)*X 1 1+(1087388949/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295493181/10000000000 : ℝ)*X 2 0+(2718472373/5000000000 : ℝ)*X 2 1+(-1816757003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287387053/10000000000 : ℝ)*X 0 0+(453674151/1000000000 : ℝ)*X 0 1+(4050254699/10000000000 : ℝ)*X 0 2+(4287387053/10000000000 : ℝ)*X 1 0+(453674151/1000000000 : ℝ)*X 1 1+(4050254699/10000000000 : ℝ)*X 1 2+(4287387053/10000000000 : ℝ)*X 2 0+(453674151/1000000000 : ℝ)*X 2 1+(4050254699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (431344756231856380933931963/196375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400504423/100000000000000 : ℝ)*(base19) + (185383413/50000000000000 : ℝ)*(base23) + (798431/6250000000000 : ℝ)*(lower2) + (59526487/100000000000000 : ℝ)*(upper3) + (7692577/25000000000000 : ℝ)*(upper5) + (3263894519650187/100000000000000 : ℝ)*(major0) + (3263894519650187/100000000000000 : ℝ)*(major1) + (815973629912547/25000000000000 : ℝ)*(major2) + (561663929762753/12500000000000 : ℝ)*(sp0) + (179732687452797/4000000000000 : ℝ)*(sp1) + (2246658608028761/50000000000000 : ℝ)*(sp2) + (508617119192347/25000000000000 : ℝ)*(sp3) + (6148722323/100000000000000 : ℝ)*(sp4) + (725622191/25000000000000 : ℝ)*(sp7) + (254308922407269/12500000000000 : ℝ)*(f.failure) + (1123329396706087/25000000000000 : ℝ)*(f.sum) + (191769426331/1885200000000000000000000000 : ℝ)*base66 + (31307195596136868037/2356500000000000000000000000000000 : ℝ)*base68 + (4374037261158309103/589125000000000000000000000000000 : ℝ)*base69 + (35204783849611368037/2356500000000000000000000000000000 : ℝ)*base72 + (5443959612323/9426000000000000000000000000 : ℝ)*base74 + (1953823085272940897/589125000000000000000000000000000 : ℝ)*base76 + (8362214487217572679/785500000000000000000000000000000 : ℝ)*base78 + (10056062538206572679/785500000000000000000000000000000 : ℝ)*base80 + (22103160693241/23565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (11742359/1250000000000000000000 : ℝ)*base89 + (11742359/1250000000000000000000 : ℝ)*base91 + (757641/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (514332735245798852950950299/98187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (434617487/50000000000000 : ℝ)*(base19) + (474830737/50000000000000 : ℝ)*(base23) + (287107737/100000000000000 : ℝ)*(lower1) + (27155251/25000000000000 : ℝ)*(upper3) + (34539233/100000000000000 : ℝ)*(lower4) + (107810503/100000000000000 : ℝ)*(upper5) + (1648853928190849/50000000000000 : ℝ)*(major0) + (1648853928190849/50000000000000 : ℝ)*(major1) + (1648853928190849/50000000000000 : ℝ)*(major2) + (575885261/50000000000000 : ℝ)*(sp2) + (567483426992857/12500000000000 : ℝ)*(sp4) + (4539866546707881/100000000000000 : ℝ)*(sp5) + (226993265725543/5000000000000 : ℝ)*(sp6) + (205554812221149/10000000000000 : ℝ)*(sp7) + (205554812221149/10000000000000 : ℝ)*(f.failure) + (567483426992857/12500000000000 : ℝ)*(f.sum) + (10548459750361/5891250000000000000000000000 : ℝ)*base66 + (8346209530289429067/392750000000000000000000000000000 : ℝ)*base67 + (3588507255501929067/392750000000000000000000000000000 : ℝ)*base69 + (18190753584485429067/392750000000000000000000000000000 : ℝ)*base71 + (4592439398473/11782500000000000000000000000 : ℝ)*base73 + (22204036389828820933/392750000000000000000000000000000 : ℝ)*base76 + (2366904274910429067/392750000000000000000000000000000 : ℝ)*base77 + (3373701194740429067/392750000000000000000000000000000 : ℝ)*base79 + (20293213072573/11782500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (43039/1000000000000000000000 : ℝ)*base89 + (43039/1000000000000000000000 : ℝ)*base91 + (43039/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1475_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2153/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1475_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1475_box_0 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-851802211/5000000000 : ℝ)*x 0 + (5406844161/10000000000 : ℝ)*x 1 + (5406844327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851802211/5000000000 : ℝ)^4447 ≤ (10032994597921/100000000000000 : ℝ)^3423 := by
    have hnat : (851802211 : ℕ)^4447*100000000000000^3423 ≤ 10032994597921^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851802211 5000000000 10032994597921 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406844161/10000000000 : ℝ)^4447 ≤ (22491750898961/50000000000000 : ℝ)^3423 := by
    have hnat : (5406844161 : ℕ)^4447*50000000000000^3423 ≤ 22491750898961^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406844161 10000000000 22491750898961 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406844327/10000000000 : ℝ)^4447 ≤ (44983503592151/100000000000000 : ℝ)^3423 := by
    have hnat : (5406844327 : ℕ)^4447*100000000000000^3423 ≤ 44983503592151^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406844327 10000000000 44983503592151 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-851802211/5000000000 : ℝ), (5406844161/10000000000 : ℝ), (5406844327/10000000000 : ℝ)] ![(10032994597921/100000000000000 : ℝ), (22491750898961/50000000000000 : ℝ), (44983503592151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-851802211/5000000000 : ℝ)|^4447 ≤ (10032994597921/100000000000000 : ℝ)^3423
        have hw : |(-851802211/5000000000 : ℝ)|=(851802211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406844161/10000000000 : ℝ)|^4447 ≤ (22491750898961/50000000000000 : ℝ)^3423
        have hw : |(5406844161/10000000000 : ℝ)|=(5406844161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406844327/10000000000 : ℝ)|^4447 ≤ (44983503592151/100000000000000 : ℝ)^3423
        have hw : |(5406844327/10000000000 : ℝ)|=(5406844327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_1 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054024713/2000000000 : ℝ)*x 0 + (-473236099/2500000000 : ℝ)*x 1 + (5406844157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054024713/2000000000 : ℝ)^4447 ≤ (43511365573893/100000000000000 : ℝ)^3423 := by
    have hnat : (1054024713 : ℕ)^4447*100000000000000^3423 ≤ 43511365573893^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054024713 2000000000 43511365573893 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473236099/2500000000 : ℝ)^4447 ≤ (1438141581009/12500000000000 : ℝ)^3423 := by
    have hnat : (473236099 : ℕ)^4447*12500000000000^3423 ≤ 1438141581009^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473236099 2500000000 1438141581009 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406844157/10000000000 : ℝ)^4447 ≤ (702867214917/1562500000000 : ℝ)^3423 := by
    have hnat : (5406844157 : ℕ)^4447*1562500000000^3423 ≤ 702867214917^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406844157 10000000000 702867214917 1562500000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054024713/2000000000 : ℝ), (-473236099/2500000000 : ℝ), (5406844157/10000000000 : ℝ)] ![(43511365573893/100000000000000 : ℝ), (1438141581009/12500000000000 : ℝ), (702867214917/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054024713/2000000000 : ℝ)|^4447 ≤ (43511365573893/100000000000000 : ℝ)^3423
        have hw : |(1054024713/2000000000 : ℝ)|=(1054024713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473236099/2500000000 : ℝ)|^4447 ≤ (1438141581009/12500000000000 : ℝ)^3423
        have hw : |(-473236099/2500000000 : ℝ)|=(473236099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406844157/10000000000 : ℝ)|^4447 ≤ (702867214917/1562500000000 : ℝ)^3423
        have hw : |(5406844157/10000000000 : ℝ)|=(5406844157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_2 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658765469/1250000000 : ℝ)*x 0 + (5406843423/10000000000 : ℝ)*x 1 + (-1892945147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658765469/1250000000 : ℝ)^4447 ≤ (1740454703187/4000000000000 : ℝ)^3423 := by
    have hnat : (658765469 : ℕ)^4447*4000000000000^3423 ≤ 1740454703187^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658765469 1250000000 1740454703187 4000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406843423/10000000000 : ℝ)^4447 ≤ (11245873455293/25000000000000 : ℝ)^3423 := by
    have hnat : (5406843423 : ℕ)^4447*25000000000000^3423 ≤ 11245873455293^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406843423 10000000000 11245873455293 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1892945147/10000000000 : ℝ)^4447 ≤ (5752569289031/50000000000000 : ℝ)^3423 := by
    have hnat : (1892945147 : ℕ)^4447*50000000000000^3423 ≤ 5752569289031^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892945147 10000000000 5752569289031 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658765469/1250000000 : ℝ), (5406843423/10000000000 : ℝ), (-1892945147/10000000000 : ℝ)] ![(1740454703187/4000000000000 : ℝ), (11245873455293/25000000000000 : ℝ), (5752569289031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658765469/1250000000 : ℝ)|^4447 ≤ (1740454703187/4000000000000 : ℝ)^3423
        have hw : |(658765469/1250000000 : ℝ)|=(658765469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406843423/10000000000 : ℝ)|^4447 ≤ (11245873455293/25000000000000 : ℝ)^3423
        have hw : |(5406843423/10000000000 : ℝ)|=(5406843423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1892945147/10000000000 : ℝ)|^4447 ≤ (5752569289031/50000000000000 : ℝ)^3423
        have hw : |(-1892945147/10000000000 : ℝ)|=(1892945147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_3 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4492177993/10000000000 : ℝ)*x 0 + (2096062491/5000000000 : ℝ)*x 1 + (4192124821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492177993/10000000000 : ℝ)^4447 ≤ (1104939518031/3125000000000 : ℝ)^3423 := by
    have hnat : (4492177993 : ℕ)^4447*3125000000000^3423 ≤ 1104939518031^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492177993 10000000000 1104939518031 3125000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2096062491/5000000000 : ℝ)^4447 ≤ (32320968513469/100000000000000 : ℝ)^3423 := by
    have hnat : (2096062491 : ℕ)^4447*100000000000000^3423 ≤ 32320968513469^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096062491 5000000000 32320968513469 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4192124821/10000000000 : ℝ)^4447 ≤ (32320966900833/100000000000000 : ℝ)^3423 := by
    have hnat : (4192124821 : ℕ)^4447*100000000000000^3423 ≤ 32320966900833^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192124821 10000000000 32320966900833 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492177993/10000000000 : ℝ), (2096062491/5000000000 : ℝ), (4192124821/10000000000 : ℝ)] ![(1104939518031/3125000000000 : ℝ), (32320968513469/100000000000000 : ℝ), (32320966900833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492177993/10000000000 : ℝ)|^4447 ≤ (1104939518031/3125000000000 : ℝ)^3423
        have hw : |(4492177993/10000000000 : ℝ)|=(4492177993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2096062491/5000000000 : ℝ)|^4447 ≤ (32320968513469/100000000000000 : ℝ)^3423
        have hw : |(2096062491/5000000000 : ℝ)|=(2096062491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4192124821/10000000000 : ℝ)|^4447 ≤ (32320966900833/100000000000000 : ℝ)^3423
        have hw : |(4192124821/10000000000 : ℝ)|=(4192124821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_4 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-537514067/2500000000 : ℝ)*x 0 + (262111121/500000000 : ℝ)*x 1 + (5242223141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537514067/2500000000 : ℝ)^4447 ≤ (848457994369/6250000000000 : ℝ)^3423 := by
    have hnat : (537514067 : ℕ)^4447*6250000000000^3423 ≤ 848457994369^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537514067 2500000000 848457994369 6250000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262111121/500000000 : ℝ)^4447 ≤ (4321233217573/10000000000000 : ℝ)^3423 := by
    have hnat : (262111121 : ℕ)^4447*10000000000000^3423 ≤ 4321233217573^3423*500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262111121 500000000 4321233217573 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242223141/10000000000 : ℝ)^4447 ≤ (43212339896983/100000000000000 : ℝ)^3423 := by
    have hnat : (5242223141 : ℕ)^4447*100000000000000^3423 ≤ 43212339896983^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242223141 10000000000 43212339896983 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537514067/2500000000 : ℝ), (262111121/500000000 : ℝ), (5242223141/10000000000 : ℝ)] ![(848457994369/6250000000000 : ℝ), (4321233217573/10000000000000 : ℝ), (43212339896983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537514067/2500000000 : ℝ)|^4447 ≤ (848457994369/6250000000000 : ℝ)^3423
        have hw : |(-537514067/2500000000 : ℝ)|=(537514067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262111121/500000000 : ℝ)|^4447 ≤ (4321233217573/10000000000000 : ℝ)^3423
        have hw : |(262111121/500000000 : ℝ)|=(262111121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242223141/10000000000 : ℝ)|^4447 ≤ (43212339896983/100000000000000 : ℝ)^3423
        have hw : |(5242223141/10000000000 : ℝ)|=(5242223141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_5 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215402761/400000000 : ℝ)*x 0 + (-1960248167/10000000000 : ℝ)*x 1 + (262111159/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215402761/400000000 : ℝ)^4447 ≤ (22374142435089/50000000000000 : ℝ)^3423 := by
    have hnat : (215402761 : ℕ)^4447*50000000000000^3423 ≤ 22374142435089^3423*400000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215402761 400000000 22374142435089 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960248167/10000000000 : ℝ)^4447 ≤ (12039374793709/100000000000000 : ℝ)^3423 := by
    have hnat : (1960248167 : ℕ)^4447*100000000000000^3423 ≤ 12039374793709^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960248167 10000000000 12039374793709 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262111159/500000000 : ℝ)^4447 ≤ (43212340314637/100000000000000 : ℝ)^3423 := by
    have hnat : (262111159 : ℕ)^4447*100000000000000^3423 ≤ 43212340314637^3423*500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262111159 500000000 43212340314637 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215402761/400000000 : ℝ), (-1960248167/10000000000 : ℝ), (262111159/500000000 : ℝ)] ![(22374142435089/50000000000000 : ℝ), (12039374793709/100000000000000 : ℝ), (43212340314637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215402761/400000000 : ℝ)|^4447 ≤ (22374142435089/50000000000000 : ℝ)^3423
        have hw : |(215402761/400000000 : ℝ)|=(215402761/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960248167/10000000000 : ℝ)|^4447 ≤ (12039374793709/100000000000000 : ℝ)^3423
        have hw : |(-1960248167/10000000000 : ℝ)|=(1960248167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262111159/500000000 : ℝ)|^4447 ≤ (43212340314637/100000000000000 : ℝ)^3423
        have hw : |(262111159/500000000 : ℝ)|=(262111159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_6 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346267377/2500000000 : ℝ)*x 0 + (1048444553/2000000000 : ℝ)*x 1 + (-1960248071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346267377/2500000000 : ℝ)^4447 ≤ (11187072521109/25000000000000 : ℝ)^3423 := by
    have hnat : (1346267377 : ℕ)^4447*25000000000000^3423 ≤ 11187072521109^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346267377 2500000000 11187072521109 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048444553/2000000000 : ℝ)^4447 ≤ (8642467174073/20000000000000 : ℝ)^3423 := by
    have hnat : (1048444553 : ℕ)^4447*20000000000000^3423 ≤ 8642467174073^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048444553 2000000000 8642467174073 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960248071/10000000000 : ℝ)^4447 ≤ (12039374027717/100000000000000 : ℝ)^3423 := by
    have hnat : (1960248071 : ℕ)^4447*100000000000000^3423 ≤ 12039374027717^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960248071 10000000000 12039374027717 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346267377/2500000000 : ℝ), (1048444553/2000000000 : ℝ), (-1960248071/10000000000 : ℝ)] ![(11187072521109/25000000000000 : ℝ), (8642467174073/20000000000000 : ℝ), (12039374027717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346267377/2500000000 : ℝ)|^4447 ≤ (11187072521109/25000000000000 : ℝ)^3423
        have hw : |(1346267377/2500000000 : ℝ)|=(1346267377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048444553/2000000000 : ℝ)|^4447 ≤ (8642467174073/20000000000000 : ℝ)^3423
        have hw : |(1048444553/2000000000 : ℝ)|=(1048444553/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960248071/10000000000 : ℝ)|^4447 ≤ (12039374027717/100000000000000 : ℝ)^3423
        have hw : |(-1960248071/10000000000 : ℝ)|=(1960248071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_7 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (816045819/2000000000 : ℝ)*x 0 + (4397959833/10000000000 : ℝ)*x 1 + (879592019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (816045819/2000000000 : ℝ)^4447 ≤ (31204680828117/100000000000000 : ℝ)^3423 := by
    have hnat : (816045819 : ℕ)^4447*100000000000000^3423 ≤ 31204680828117^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816045819 2000000000 31204680828117 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397959833/10000000000 : ℝ)^4447 ≤ (4299707280627/12500000000000 : ℝ)^3423 := by
    have hnat : (4397959833 : ℕ)^4447*12500000000000^3423 ≤ 4299707280627^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397959833 10000000000 4299707280627 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879592019/2000000000 : ℝ)^4447 ≤ (17198830453603/50000000000000 : ℝ)^3423 := by
    have hnat : (879592019 : ℕ)^4447*50000000000000^3423 ≤ 17198830453603^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879592019 2000000000 17198830453603 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(816045819/2000000000 : ℝ), (4397959833/10000000000 : ℝ), (879592019/2000000000 : ℝ)] ![(31204680828117/100000000000000 : ℝ), (4299707280627/12500000000000 : ℝ), (17198830453603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(816045819/2000000000 : ℝ)|^4447 ≤ (31204680828117/100000000000000 : ℝ)^3423
        have hw : |(816045819/2000000000 : ℝ)|=(816045819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397959833/10000000000 : ℝ)|^4447 ≤ (4299707280627/12500000000000 : ℝ)^3423
        have hw : |(4397959833/10000000000 : ℝ)|=(4397959833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879592019/2000000000 : ℝ)|^4447 ≤ (17198830453603/50000000000000 : ℝ)^3423
        have hw : |(879592019/2000000000 : ℝ)|=(879592019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_8 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027962941/5000000000 : ℝ)*x 0 + (5127316351/10000000000 : ℝ)*x 1 + (5427403427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027962941/5000000000 : ℝ)^4447 ≤ (320207666513/2500000000000 : ℝ)^3423 := by
    have hnat : (1027962941 : ℕ)^4447*2500000000000^3423 ≤ 320207666513^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027962941 5000000000 320207666513 2500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127316351/10000000000 : ℝ)^4447 ≤ (20992924137939/50000000000000 : ℝ)^3423 := by
    have hnat : (5127316351 : ℕ)^4447*50000000000000^3423 ≤ 20992924137939^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127316351 10000000000 20992924137939 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427403427/10000000000 : ℝ)^4447 ≤ (45205845054907/100000000000000 : ℝ)^3423 := by
    have hnat : (5427403427 : ℕ)^4447*100000000000000^3423 ≤ 45205845054907^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427403427 10000000000 45205845054907 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027962941/5000000000 : ℝ), (5127316351/10000000000 : ℝ), (5427403427/10000000000 : ℝ)] ![(320207666513/2500000000000 : ℝ), (20992924137939/50000000000000 : ℝ), (45205845054907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027962941/5000000000 : ℝ)|^4447 ≤ (320207666513/2500000000000 : ℝ)^3423
        have hw : |(-1027962941/5000000000 : ℝ)|=(1027962941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127316351/10000000000 : ℝ)|^4447 ≤ (20992924137939/50000000000000 : ℝ)^3423
        have hw : |(5127316351/10000000000 : ℝ)|=(5127316351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427403427/10000000000 : ℝ)|^4447 ≤ (45205845054907/100000000000000 : ℝ)^3423
        have hw : |(5427403427/10000000000 : ℝ)|=(5427403427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_9 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255760161/10000000000 : ℝ)*x 0 + (-235535407/1250000000 : ℝ)*x 1 + (1085480683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255760161/10000000000 : ℝ)^4447 ≤ (8671473000809/20000000000000 : ℝ)^3423 := by
    have hnat : (5255760161 : ℕ)^4447*20000000000000^3423 ≤ 8671473000809^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255760161 10000000000 8671473000809 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235535407/1250000000 : ℝ)^4447 ≤ (2859197515147/25000000000000 : ℝ)^3423 := by
    have hnat : (235535407 : ℕ)^4447*25000000000000^3423 ≤ 2859197515147^3423*1250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235535407 1250000000 2859197515147 25000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085480683/2000000000 : ℝ)^4447 ≤ (45205844925057/100000000000000 : ℝ)^3423 := by
    have hnat : (1085480683 : ℕ)^4447*100000000000000^3423 ≤ 45205844925057^3423*2000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085480683 2000000000 45205844925057 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255760161/10000000000 : ℝ), (-235535407/1250000000 : ℝ), (1085480683/2000000000 : ℝ)] ![(8671473000809/20000000000000 : ℝ), (2859197515147/25000000000000 : ℝ), (45205844925057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255760161/10000000000 : ℝ)|^4447 ≤ (8671473000809/20000000000000 : ℝ)^3423
        have hw : |(5255760161/10000000000 : ℝ)|=(5255760161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235535407/1250000000 : ℝ)|^4447 ≤ (2859197515147/25000000000000 : ℝ)^3423
        have hw : |(-235535407/1250000000 : ℝ)|=(235535407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085480683/2000000000 : ℝ)|^4447 ≤ (45205844925057/100000000000000 : ℝ)^3423
        have hw : |(1085480683/2000000000 : ℝ)|=(1085480683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_10 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627880339/5000000000 : ℝ)*x 0 + (1356850717/2500000000 : ℝ)*x 1 + (-1884283303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627880339/5000000000 : ℝ)^4447 ≤ (43357370544917/100000000000000 : ℝ)^3423 := by
    have hnat : (2627880339 : ℕ)^4447*100000000000000^3423 ≤ 43357370544917^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627880339 5000000000 43357370544917 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356850717/2500000000 : ℝ)^4447 ≤ (22602919503017/50000000000000 : ℝ)^3423 := by
    have hnat : (1356850717 : ℕ)^4447*50000000000000^3423 ≤ 22602919503017^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356850717 2500000000 22602919503017 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884283303/10000000000 : ℝ)^4447 ≤ (11436790431197/100000000000000 : ℝ)^3423 := by
    have hnat : (1884283303 : ℕ)^4447*100000000000000^3423 ≤ 11436790431197^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884283303 10000000000 11436790431197 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627880339/5000000000 : ℝ), (1356850717/2500000000 : ℝ), (-1884283303/10000000000 : ℝ)] ![(43357370544917/100000000000000 : ℝ), (22602919503017/50000000000000 : ℝ), (11436790431197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627880339/5000000000 : ℝ)|^4447 ≤ (43357370544917/100000000000000 : ℝ)^3423
        have hw : |(2627880339/5000000000 : ℝ)|=(2627880339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356850717/2500000000 : ℝ)|^4447 ≤ (22602919503017/50000000000000 : ℝ)^3423
        have hw : |(1356850717/2500000000 : ℝ)|=(1356850717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884283303/10000000000 : ℝ)|^4447 ≤ (11436790431197/100000000000000 : ℝ)^3423
        have hw : |(-1884283303/10000000000 : ℝ)|=(1884283303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_11 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4542469143/10000000000 : ℝ)*x 0 + (2083193621/5000000000 : ℝ)*x 1 + (4166387451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4542469143/10000000000 : ℝ)^4447 ≤ (35873184176821/100000000000000 : ℝ)^3423 := by
    have hnat : (4542469143 : ℕ)^4447*100000000000000^3423 ≤ 35873184176821^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542469143 10000000000 35873184176821 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083193621/5000000000 : ℝ)^4447 ≤ (6412681372481/20000000000000 : ℝ)^3423 := by
    have hnat : (2083193621 : ℕ)^4447*20000000000000^3423 ≤ 6412681372481^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083193621 5000000000 6412681372481 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166387451/10000000000 : ℝ)^4447 ≤ (32063408951973/100000000000000 : ℝ)^3423 := by
    have hnat : (4166387451 : ℕ)^4447*100000000000000^3423 ≤ 32063408951973^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166387451 10000000000 32063408951973 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4542469143/10000000000 : ℝ), (2083193621/5000000000 : ℝ), (4166387451/10000000000 : ℝ)] ![(35873184176821/100000000000000 : ℝ), (6412681372481/20000000000000 : ℝ), (32063408951973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4542469143/10000000000 : ℝ)|^4447 ≤ (35873184176821/100000000000000 : ℝ)^3423
        have hw : |(4542469143/10000000000 : ℝ)|=(4542469143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083193621/5000000000 : ℝ)|^4447 ≤ (6412681372481/20000000000000 : ℝ)^3423
        have hw : |(2083193621/5000000000 : ℝ)|=(2083193621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166387451/10000000000 : ℝ)|^4447 ≤ (32063408951973/100000000000000 : ℝ)^3423
        have hw : |(4166387451/10000000000 : ℝ)|=(4166387451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_12 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797896367/10000000000 : ℝ)*x 0 + (1379480049/2500000000 : ℝ)*x 1 + (5227237291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797896367/10000000000 : ℝ)^4447 ≤ (538016291381/5000000000000 : ℝ)^3423 := by
    have hnat : (1797896367 : ℕ)^4447*5000000000000^3423 ≤ 538016291381^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797896367 10000000000 538016291381 5000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379480049/2500000000 : ℝ)^4447 ≤ (4618775039053/10000000000000 : ℝ)^3423 := by
    have hnat : (1379480049 : ℕ)^4447*10000000000000^3423 ≤ 4618775039053^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379480049 2500000000 4618775039053 10000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227237291/10000000000 : ℝ)^4447 ≤ (21525961884893/50000000000000 : ℝ)^3423 := by
    have hnat : (5227237291 : ℕ)^4447*50000000000000^3423 ≤ 21525961884893^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227237291 10000000000 21525961884893 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797896367/10000000000 : ℝ), (1379480049/2500000000 : ℝ), (5227237291/10000000000 : ℝ)] ![(538016291381/5000000000000 : ℝ), (4618775039053/10000000000000 : ℝ), (21525961884893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797896367/10000000000 : ℝ)|^4447 ≤ (538016291381/5000000000000 : ℝ)^3423
        have hw : |(-1797896367/10000000000 : ℝ)|=(1797896367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379480049/2500000000 : ℝ)|^4447 ≤ (4618775039053/10000000000000 : ℝ)^3423
        have hw : |(1379480049/2500000000 : ℝ)|=(1379480049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227237291/10000000000 : ℝ)|^4447 ≤ (21525961884893/50000000000000 : ℝ)^3423
        have hw : |(5227237291/10000000000 : ℝ)|=(5227237291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_13 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697765491/5000000000 : ℝ)*x 0 + (-983095597/5000000000 : ℝ)*x 1 + (2613618627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697765491/5000000000 : ℝ)^4447 ≤ (5607657550693/12500000000000 : ℝ)^3423 := by
    have hnat : (2697765491 : ℕ)^4447*12500000000000^3423 ≤ 5607657550693^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697765491 5000000000 5607657550693 12500000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983095597/5000000000 : ℝ)^4447 ≤ (12086816201991/100000000000000 : ℝ)^3423 := by
    have hnat : (983095597 : ℕ)^4447*100000000000000^3423 ≤ 12086816201991^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983095597 5000000000 12086816201991 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613618627/5000000000 : ℝ)^4447 ≤ (43051923373889/100000000000000 : ℝ)^3423 := by
    have hnat : (2613618627 : ℕ)^4447*100000000000000^3423 ≤ 43051923373889^3423*5000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613618627 5000000000 43051923373889 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697765491/5000000000 : ℝ), (-983095597/5000000000 : ℝ), (2613618627/5000000000 : ℝ)] ![(5607657550693/12500000000000 : ℝ), (12086816201991/100000000000000 : ℝ), (43051923373889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697765491/5000000000 : ℝ)|^4447 ≤ (5607657550693/12500000000000 : ℝ)^3423
        have hw : |(2697765491/5000000000 : ℝ)|=(2697765491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983095597/5000000000 : ℝ)|^4447 ≤ (12086816201991/100000000000000 : ℝ)^3423
        have hw : |(-983095597/5000000000 : ℝ)|=(983095597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613618627/5000000000 : ℝ)|^4447 ≤ (43051923373889/100000000000000 : ℝ)^3423
        have hw : |(2613618627/5000000000 : ℝ)|=(2613618627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_14 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395531533/10000000000 : ℝ)*x 0 + (5227237141/10000000000 : ℝ)*x 1 + (-9830953/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395531533/10000000000 : ℝ)^4447 ≤ (8972253271471/20000000000000 : ℝ)^3423 := by
    have hnat : (5395531533 : ℕ)^4447*20000000000000^3423 ≤ 8972253271471^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395531533 10000000000 8972253271471 20000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227237141/10000000000 : ℝ)^4447 ≤ (21525961082399/50000000000000 : ℝ)^3423 := by
    have hnat : (5227237141 : ℕ)^4447*50000000000000^3423 ≤ 21525961082399^3423*10000000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227237141 10000000000 21525961082399 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9830953/50000000 : ℝ)^4447 ≤ (12086811458121/100000000000000 : ℝ)^3423 := by
    have hnat : (9830953 : ℕ)^4447*100000000000000^3423 ≤ 12086811458121^3423*50000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9830953 50000000 12086811458121 100000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395531533/10000000000 : ℝ), (5227237141/10000000000 : ℝ), (-9830953/50000000 : ℝ)] ![(8972253271471/20000000000000 : ℝ), (21525961082399/50000000000000 : ℝ), (12086811458121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395531533/10000000000 : ℝ)|^4447 ≤ (8972253271471/20000000000000 : ℝ)^3423
        have hw : |(5395531533/10000000000 : ℝ)|=(5395531533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227237141/10000000000 : ℝ)|^4447 ≤ (21525961082399/50000000000000 : ℝ)^3423
        have hw : |(5227237141/10000000000 : ℝ)|=(5227237141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9830953/50000000 : ℝ)|^4447 ≤ (12086811458121/100000000000000 : ℝ)^3423
        have hw : |(-9830953/50000000 : ℝ)|=(9830953/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1475_box_15 (p : ℝ) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (101046707/250000000 : ℝ)*x 0 + (88333543/200000000 : ℝ)*x 1 + (1104168991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101046707/250000000 : ℝ)^4447 ≤ (963252472261/3125000000000 : ℝ)^3423 := by
    have hnat : (101046707 : ℕ)^4447*3125000000000^3423 ≤ 963252472261^3423*250000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101046707 250000000 963252472261 3125000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88333543/200000000 : ℝ)^4447 ≤ (17293983232519/50000000000000 : ℝ)^3423 := by
    have hnat : (88333543 : ℕ)^4447*50000000000000^3423 ≤ 17293983232519^3423*200000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88333543 200000000 17293983232519 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104168991/2500000000 : ℝ)^4447 ≤ (17293977199367/50000000000000 : ℝ)^3423 := by
    have hnat : (1104168991 : ℕ)^4447*50000000000000^3423 ≤ 17293977199367^3423*2500000000^4447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104168991 2500000000 17293977199367 50000000000000 4447 3423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4447/1024 : ℝ)) 4447 3423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(101046707/250000000 : ℝ), (88333543/200000000 : ℝ), (1104168991/2500000000 : ℝ)] ![(963252472261/3125000000000 : ℝ), (17293983232519/50000000000000 : ℝ), (17293977199367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(101046707/250000000 : ℝ)|^4447 ≤ (963252472261/3125000000000 : ℝ)^3423
        have hw : |(101046707/250000000 : ℝ)|=(101046707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88333543/200000000 : ℝ)|^4447 ≤ (17293983232519/50000000000000 : ℝ)^3423
        have hw : |(88333543/200000000 : ℝ)|=(88333543/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104168991/2500000000 : ℝ)|^4447 ≤ (17293977199367/50000000000000 : ℝ)^3423
        have hw : |(1104168991/2500000000 : ℝ)|=(1104168991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1475_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2153/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63697/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29227/50000 : ℝ) ∧ (9989/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85761/100000 : ℝ) := by
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
  have lower0 : (2153/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2153/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2153/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2153/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2153/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2153/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2153/20000 : ℝ) ^ (4445/1024 : ℝ) ≤ (785338466882937/12500000000000000000 : ℝ) := by
    have hpowers : (2153/20000 : ℝ)^4445 ≤ (785338466882937/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2153 : ℕ)^4445*12500000000000000000^1024 ≤ 785338466882937^1024*20000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2153 20000 785338466882937 12500000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2153/20000 : ℝ)) (X := (785338466882937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4445/1024 : ℝ) ≤ (30353618572116671/100000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4445 ≤ (30353618572116671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4445*100000000000000000000^1024 ≤ 30353618572116671^1024*50000^4445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 30353618572116671 100000000000000000000 4445 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (30353618572116671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250785338466882937/6250000000000000000 : ℝ) ≤ (2500072364248163/2500000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (6250785338466882937/6250000000000000000 : ℝ)^1024 ≤ (2500072364248163/2500000000000000 : ℝ)^4445 := by
      have hnat : (6250785338466882937 : ℕ)^1024*2500000000000000^4445 ≤ 2500072364248163^4445*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250785338466882937 6250000000000000000 2500072364248163 2500000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500072364248163/2500000000000000 : ℝ)) (X := (6250785338466882937/6250000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036636326307180167/100000000000000000000 : ℝ) ≤ (2000168775299269/2000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (100036636326307180167/100000000000000000000 : ℝ)^1024 ≤ (2000168775299269/2000000000000000 : ℝ)^4445 := by
      have hnat : (100036636326307180167 : ℕ)^1024*2000000000000000^4445 ≤ 2000168775299269^4445*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036636326307180167 100000000000000000000 2000168775299269 2000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000168775299269/2000000000000000 : ℝ)) (X := (100036636326307180167/100000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030353618572116671/50000000000000000000 : ℝ) ≤ (5000699148000019/5000000000000000 : ℝ) ^ (4445/1024 : ℝ) := by
    have hpowers : (50030353618572116671/50000000000000000000 : ℝ)^1024 ≤ (5000699148000019/5000000000000000 : ℝ)^4445 := by
      have hnat : (50030353618572116671 : ℕ)^1024*5000000000000000^4445 ≤ 5000699148000019^4445*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030353618572116671 50000000000000000000 5000699148000019 5000000000000000 1024 4445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000699148000019/5000000000000000 : ℝ)) (X := (50030353618572116671/50000000000000000000 : ℝ)) (by norm_num) 4445 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(785338466882937/12500000000000000000 : ℝ) ≤ ((23539713200531943989/23545000000000000000 : ℝ)+2*(554419503693/470900000000000 : ℝ)*(2153/20000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (23539713200531943989/23545000000000000000 : ℝ)+2*(554419503693/470900000000000 : ℝ)*(2153/20000 : ℝ)=(2500072364248163/2500000000000000 : ℝ) by norm_num, show 1+2*(785338466882937/12500000000000000000 : ℝ)=(6250785338466882937/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30353618572116671/100000000000000000000 : ℝ)+(785338466882937/12500000000000000000 : ℝ) ≤ ((23539713200531943989/23545000000000000000 : ℝ)+(554419503693/470900000000000 : ℝ)*((7737/50000 : ℝ)+(2153/20000 : ℝ)))^(4445/1024 : ℝ) := by
    rw [show (23539713200531943989/23545000000000000000 : ℝ)+(554419503693/470900000000000 : ℝ)*((7737/50000 : ℝ)+(2153/20000 : ℝ))=(2000168775299269/2000000000000000 : ℝ) by norm_num, show 1+(30353618572116671/100000000000000000000 : ℝ)+(785338466882937/12500000000000000000 : ℝ)=(100036636326307180167/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30353618572116671/100000000000000000000 : ℝ) ≤ ((23539713200531943989/23545000000000000000 : ℝ)+2*(554419503693/470900000000000 : ℝ)*(7737/50000 : ℝ))^(4445/1024 : ℝ) := by
    rw [show (23539713200531943989/23545000000000000000 : ℝ)+2*(554419503693/470900000000000 : ℝ)*(7737/50000 : ℝ)=(5000699148000019/5000000000000000 : ℝ) by norm_num, show 1+2*(30353618572116671/100000000000000000000 : ℝ)=(50030353618572116671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23539713200531943989/23545000000000000000 : ℝ)*(X 1 0+X 2 0)+(554419503693/470900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (2153/20000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (23539713200531943989/23545000000000000000 : ℝ)) (alpha := (554419503693/470900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23539713200531943989/23545000000000000000 : ℝ)*(X 0 1+X 2 1)+(554419503693/470900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (2153/20000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (23539713200531943989/23545000000000000000 : ℝ)) (alpha := (554419503693/470900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23539713200531943989/23545000000000000000 : ℝ)*(X 0 2+X 1 2)+(554419503693/470900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4445/1024 : ℝ)) (lo := (2153/20000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (23539713200531943989/23545000000000000000 : ℝ)) (alpha := (554419503693/470900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-851802211/5000000000 : ℝ)*X 0 0+(5406844161/10000000000 : ℝ)*X 0 1+(5406844327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054024713/2000000000 : ℝ)*X 1 0+(-473236099/2500000000 : ℝ)*X 1 1+(5406844157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((658765469/1250000000 : ℝ)*X 2 0+(5406843423/10000000000 : ℝ)*X 2 1+(-1892945147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4492177993/10000000000 : ℝ)*X 0 0+(2096062491/5000000000 : ℝ)*X 0 1+(4192124821/10000000000 : ℝ)*X 0 2+(4492177993/10000000000 : ℝ)*X 1 0+(2096062491/5000000000 : ℝ)*X 1 1+(4192124821/10000000000 : ℝ)*X 1 2+(4492177993/10000000000 : ℝ)*X 2 0+(2096062491/5000000000 : ℝ)*X 2 1+(4192124821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-537514067/2500000000 : ℝ)*X 0 0+(262111121/500000000 : ℝ)*X 0 1+(5242223141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((215402761/400000000 : ℝ)*X 1 0+(-1960248167/10000000000 : ℝ)*X 1 1+(262111159/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1346267377/2500000000 : ℝ)*X 2 0+(1048444553/2000000000 : ℝ)*X 2 1+(-1960248071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((816045819/2000000000 : ℝ)*X 0 0+(4397959833/10000000000 : ℝ)*X 0 1+(879592019/2000000000 : ℝ)*X 0 2+(816045819/2000000000 : ℝ)*X 1 0+(4397959833/10000000000 : ℝ)*X 1 1+(879592019/2000000000 : ℝ)*X 1 2+(816045819/2000000000 : ℝ)*X 2 0+(4397959833/10000000000 : ℝ)*X 2 1+(879592019/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1027962941/5000000000 : ℝ)*X 0 0+(5127316351/10000000000 : ℝ)*X 0 1+(5427403427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5255760161/10000000000 : ℝ)*X 1 0+(-235535407/1250000000 : ℝ)*X 1 1+(1085480683/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2627880339/5000000000 : ℝ)*X 2 0+(1356850717/2500000000 : ℝ)*X 2 1+(-1884283303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4542469143/10000000000 : ℝ)*X 0 0+(2083193621/5000000000 : ℝ)*X 0 1+(4166387451/10000000000 : ℝ)*X 0 2+(4542469143/10000000000 : ℝ)*X 1 0+(2083193621/5000000000 : ℝ)*X 1 1+(4166387451/10000000000 : ℝ)*X 1 2+(4542469143/10000000000 : ℝ)*X 2 0+(2083193621/5000000000 : ℝ)*X 2 1+(4166387451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1797896367/10000000000 : ℝ)*X 0 0+(1379480049/2500000000 : ℝ)*X 0 1+(5227237291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2697765491/5000000000 : ℝ)*X 1 0+(-983095597/5000000000 : ℝ)*X 1 1+(2613618627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5395531533/10000000000 : ℝ)*X 2 0+(5227237141/10000000000 : ℝ)*X 2 1+(-9830953/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((101046707/250000000 : ℝ)*X 0 0+(88333543/200000000 : ℝ)*X 0 1+(1104168991/2500000000 : ℝ)*X 0 2+(101046707/250000000 : ℝ)*X 1 0+(88333543/200000000 : ℝ)*X 1 1+(1104168991/2500000000 : ℝ)*X 1 2+(101046707/250000000 : ℝ)*X 2 0+(88333543/200000000 : ℝ)*X 2 1+(1104168991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1475_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63697/100000 : ℝ) ≤ (-749844476552280440090970052028157/1177250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23139543/50000000000000 : ℝ)*(lower2) + (110030171/100000000000000 : ℝ)*(lower3) + (5295221/50000000000000 : ℝ)*(upper5) + (433638549682557/20000000000000 : ℝ)*(major0) + (433638549682557/20000000000000 : ℝ)*(major1) + (1084096374206393/50000000000000 : ℝ)*(major2) + (856843543/100000000000000 : ℝ)*(sp2) + (150306075766377/5000000000000 : ℝ)*(sp4) + (751510067435943/25000000000000 : ℝ)*(sp5) + (3006124547753627/100000000000000 : ℝ)*(sp6) + (675711447198983/50000000000000 : ℝ)*(sp7) + (388926963/10000000000000 : ℝ)*(sp12) + (85134853397/100000000000000 : ℝ)*(sp13) + (13745089139/20000000000000 : ℝ)*(sp15) + (675745809921831/50000000000000 : ℝ)*(f.failure) + (300612540459717/10000000000000 : ℝ)*(f.sum) + (161268265185897/47090000000000000000000000000 : ℝ)*base66 + (4114345063594079873/470900000000000000000000000000000 : ℝ)*base67 + (6717767386031846677/1177250000000000000000000000000000 : ℝ)*base69 + (3278629266789679873/470900000000000000000000000000000 : ℝ)*base71 + (299385113462963/47090000000000000000000000000 : ℝ)*base73 + (14024356175143846677/1177250000000000000000000000000000 : ℝ)*base75 + (2161539193935450127/470900000000000000000000000000000 : ℝ)*base78 + (1668412445619549873/470900000000000000000000000000000 : ℝ)*base79 + (6015100624893/4709000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (37737741/5000000000000000000000 : ℝ)*base89 + (37737741/5000000000000000000000 : ℝ)*base91 + (12262259/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29227/50000 : ℝ) ≤ (13763682750754737608320254831/23545000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62864799/100000000000000 : ℝ)*(lower0) + (46942297/100000000000000 : ℝ)*(upper1) + (45099929/25000000000000 : ℝ)*(upper2) + (1120960645973103/50000000000000 : ℝ)*(major0) + (1120960645973103/50000000000000 : ℝ)*(major1) + (1120960645973103/50000000000000 : ℝ)*(major2) + (191681652675833/6250000000000 : ℝ)*(sp0) + (3066906581994949/100000000000000 : ℝ)*(sp1) + (383344655620929/12500000000000 : ℝ)*(sp2) + (698720156018057/50000000000000 : ℝ)*(sp3) + (1798568451/100000000000000 : ℝ)*(sp5) + (151135595969/100000000000000 : ℝ)*(sp10) + (4124983349/50000000000000 : ℝ)*(sp11) + (1937750073/100000000000000 : ℝ)*(sp12) + (349362140500703/25000000000000 : ℝ)*(f.failure) + (15334541902817/500000000000 : ℝ)*(f.sum) + (101191788025853/23545000000000000000000000000 : ℝ)*base65 + (85966113460477867/1177250000000000000000000000000000 : ℝ)*base67 + (4231051912764272133/1177250000000000000000000000000000 : ℝ)*base70 + (5333765777794477867/1177250000000000000000000000000000 : ℝ)*base71 + (18379468050177/23545000000000000000000000000 : ℝ)*base74 + (5878353282269227867/1177250000000000000000000000000000 : ℝ)*base75 + (1208151709624022133/1177250000000000000000000000000000 : ℝ)*base78 + (3541478668241522133/1177250000000000000000000000000000 : ℝ)*base80 + (156004160192613/23545000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (22483467/2500000000000000000000 : ℝ)*base90 + (22483467/2500000000000000000000 : ℝ)*base92 + (22483467/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (9989/12500 : ℝ) ≤ (235197514914433029242228579353233/294312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35777457/100000000000000 : ℝ)*(upper0) + (49453259/100000000000000 : ℝ)*(lower3) + (57679251/100000000000000 : ℝ)*(upper4) + (609987206909401/25000000000000 : ℝ)*(major0) + (609987206909401/25000000000000 : ℝ)*(major1) + (609987206909401/25000000000000 : ℝ)*(major2) + (79789267963/100000000000000 : ℝ)*(sp1) + (2772451947/50000000000000 : ℝ)*(sp3) + (2181532463/50000000000000 : ℝ)*(sp4) + (166618449766333/5000000000000 : ℝ)*(sp8) + (3332295457107603/100000000000000 : ℝ)*(sp9) + (1666187623187783/50000000000000 : ℝ)*(sp10) + (152087879336057/10000000000000 : ℝ)*(sp11) + (94399199/5000000000000 : ℝ)*(sp12) + (95055271141529/6250000000000 : ℝ)*(f.failure) + (1666187623187783/50000000000000 : ℝ)*(f.sum) + (2601179777777/5886250000000000000000000000 : ℝ)*base66 + (2131538237247309411/588625000000000000000000000000000 : ℝ)*base68 + (2750442108712940589/588625000000000000000000000000000 : ℝ)*base69 + (1489093006415440589/588625000000000000000000000000000 : ℝ)*base71 + (12528207306079/2943125000000000000000000000 : ℝ)*base73 + (3312861505765809411/588625000000000000000000000000000 : ℝ)*base76 + (453500574774190589/588625000000000000000000000000000 : ℝ)*base77 + (4255040288596190589/588625000000000000000000000000000 : ℝ)*base79 + (63907392495501/11772500000000000000000000000 : ℝ)*base81 + (1584781/625000000000000000000 : ℝ)*base90 + (1584781/625000000000000000000 : ℝ)*base92 + (1584781/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-85761/100000 : ℝ) ≤ (-10095873336429323056632655109799/11772500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61693989/20000000000000 : ℝ)*(lower2) + (42712293/20000000000000 : ℝ)*(upper3) + (167166931/100000000000000 : ℝ)*(upper5) + (49562704359597/2000000000000 : ℝ)*(major0) + (49562704359597/2000000000000 : ℝ)*(major1) + (49562704359597/2000000000000 : ℝ)*(major2) + (46064349/12500000000000 : ℝ)*(sp0) + (155418408257/100000000000000 : ℝ)*(sp5) + (20876201227/50000000000000 : ℝ)*(sp6) + (92241822763/100000000000000 : ℝ)*(sp7) + (3440169182990919/100000000000000 : ℝ)*(sp12) + (1720007066548727/50000000000000 : ℝ)*(sp13) + (430015974887907/12500000000000 : ℝ)*(sp14) + (30891893576709/2000000000000 : ℝ)*(sp15) + (1544686920658213/100000000000000 : ℝ)*(f.failure) + (344016955150571/10000000000000 : ℝ)*(f.sum) + (365617626141/2354500000000000000000000000 : ℝ)*base66 + (59586905885312433/47090000000000000000000000000000 : ℝ)*base67 + (346693181554157567/47090000000000000000000000000000 : ℝ)*base70 + (176365442892242433/47090000000000000000000000000000 : ℝ)*base71 + (18567779388673/2354500000000000000000000000 : ℝ)*base74 + (17868031500172433/47090000000000000000000000000000 : ℝ)*base75 + (487466242388812433/47090000000000000000000000000000 : ℝ)*base77 + (480766139686012433/47090000000000000000000000000000 : ℝ)*base79 + (35503868460549/4709000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (24454857/10000000000000000000000 : ℝ)*base90 + (24454857/10000000000000000000000 : ℝ)*base92 + (24454857/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1475_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2153/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63697/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29227/50000 : ℝ) else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (85761/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1475_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1475_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63697/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29227/50000 : ℝ) else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (85761/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1475_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1475_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4445/1024 : ℝ) ≤ p) (hpb : p ≤ (4447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (160429611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10763/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63697/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29227/50000 : ℝ) else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (85761/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1475_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
