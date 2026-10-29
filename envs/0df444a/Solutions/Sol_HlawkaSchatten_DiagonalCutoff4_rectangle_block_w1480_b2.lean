-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1480_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:40.866481+00:00
-- url     : https://prove2.me/submissions/51e37bda-a9ed-4134-91c5-c7fc542253ef

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
theorem support_rectangle_w1480_s6_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-239543411/1250000000 : ℝ)*x 0 + (1359356861/2500000000 : ℝ)*x 1 + (5215850617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239543411/1250000000 : ℝ)^4457 ≤ (5853554081097/50000000000000 : ℝ)^3433 := by
    have hnat : (239543411 : ℕ)^4457*50000000000000^3433 ≤ 5853554081097^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239543411 1250000000 5853554081097 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359356861/2500000000 : ℝ)^4457 ≤ (11334602190151/25000000000000 : ℝ)^3433 := by
    have hnat : (1359356861 : ℕ)^4457*25000000000000^3433 ≤ 11334602190151^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359356861 2500000000 11334602190151 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215850617/10000000000 : ℝ)^4457 ≤ (10738620764401/25000000000000 : ℝ)^3433 := by
    have hnat : (5215850617 : ℕ)^4457*25000000000000^3433 ≤ 10738620764401^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215850617 10000000000 10738620764401 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239543411/1250000000 : ℝ), (1359356861/2500000000 : ℝ), (5215850617/10000000000 : ℝ)] ![(5853554081097/50000000000000 : ℝ), (11334602190151/25000000000000 : ℝ), (10738620764401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239543411/1250000000 : ℝ)|^4457 ≤ (5853554081097/50000000000000 : ℝ)^3433
        have hw : |(-239543411/1250000000 : ℝ)|=(239543411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359356861/2500000000 : ℝ)|^4457 ≤ (11334602190151/25000000000000 : ℝ)^3433
        have hw : |(1359356861/2500000000 : ℝ)|=(1359356861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215850617/10000000000 : ℝ)|^4457 ≤ (10738620764401/25000000000000 : ℝ)^3433
        have hw : |(5215850617/10000000000 : ℝ)|=(5215850617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669163581/1250000000 : ℝ)*x 0 + (-1014952177/5000000000 : ℝ)*x 1 + (2607925269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669163581/1250000000 : ℝ)^4457 ≤ (44429902691719/100000000000000 : ℝ)^3433 := by
    have hnat : (669163581 : ℕ)^4457*100000000000000^3433 ≤ 44429902691719^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669163581 1250000000 44429902691719 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014952177/5000000000 : ℝ)^4457 ≤ (3942379711/31250000000 : ℝ)^3433 := by
    have hnat : (1014952177 : ℕ)^4457*31250000000^3433 ≤ 3942379711^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014952177 5000000000 3942379711 31250000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607925269/5000000000 : ℝ)^4457 ≤ (42954482212949/100000000000000 : ℝ)^3433 := by
    have hnat : (2607925269 : ℕ)^4457*100000000000000^3433 ≤ 42954482212949^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607925269 5000000000 42954482212949 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669163581/1250000000 : ℝ), (-1014952177/5000000000 : ℝ), (2607925269/5000000000 : ℝ)] ![(44429902691719/100000000000000 : ℝ), (3942379711/31250000000 : ℝ), (42954482212949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669163581/1250000000 : ℝ)|^4457 ≤ (44429902691719/100000000000000 : ℝ)^3433
        have hw : |(669163581/1250000000 : ℝ)|=(669163581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1014952177/5000000000 : ℝ)|^4457 ≤ (3942379711/31250000000 : ℝ)^3433
        have hw : |(-1014952177/5000000000 : ℝ)|=(1014952177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607925269/5000000000 : ℝ)|^4457 ≤ (42954482212949/100000000000000 : ℝ)^3433
        have hw : |(2607925269/5000000000 : ℝ)|=(2607925269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214132337/400000000 : ℝ)*x 0 + (651981379/1250000000 : ℝ)*x 1 + (-1014951999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214132337/400000000 : ℝ)^4457 ≤ (11107475072217/25000000000000 : ℝ)^3433 := by
    have hnat : (214132337 : ℕ)^4457*25000000000000^3433 ≤ 11107475072217^3433*400000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214132337 400000000 11107475072217 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651981379/1250000000 : ℝ)^4457 ≤ (8590897498943/20000000000000 : ℝ)^3433 := by
    have hnat : (651981379 : ℕ)^4457*20000000000000^3433 ≤ 8590897498943^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651981379 1250000000 8590897498943 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014951999/5000000000 : ℝ)^4457 ≤ (3153903050689/25000000000000 : ℝ)^3433 := by
    have hnat : (1014951999 : ℕ)^4457*25000000000000^3433 ≤ 3153903050689^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014951999 5000000000 3153903050689 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214132337/400000000 : ℝ), (651981379/1250000000 : ℝ), (-1014951999/5000000000 : ℝ)] ![(11107475072217/25000000000000 : ℝ), (8590897498943/20000000000000 : ℝ), (3153903050689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214132337/400000000 : ℝ)|^4457 ≤ (11107475072217/25000000000000 : ℝ)^3433
        have hw : |(214132337/400000000 : ℝ)|=(214132337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651981379/1250000000 : ℝ)|^4457 ≤ (8590897498943/20000000000000 : ℝ)^3433
        have hw : |(651981379/1250000000 : ℝ)|=(651981379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1014951999/5000000000 : ℝ)|^4457 ≤ (3153903050689/25000000000000 : ℝ)^3433
        have hw : |(-1014951999/5000000000 : ℝ)|=(1014951999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267806943/625000000 : ℝ)*x 0 + (2022739909/5000000000 : ℝ)*x 1 + (226830767/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267806943/625000000 : ℝ)^4457 ≤ (2079873522549/6250000000000 : ℝ)^3433 := by
    have hnat : (267806943 : ℕ)^4457*6250000000000^3433 ≤ 2079873522549^3433*625000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267806943 625000000 2079873522549 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022739909/5000000000 : ℝ)^4457 ≤ (30884211447367/100000000000000 : ℝ)^3433 := by
    have hnat : (2022739909 : ℕ)^4457*100000000000000^3433 ≤ 30884211447367^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022739909 5000000000 30884211447367 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226830767/500000000 : ℝ)^4457 ≤ (286702497477/800000000000 : ℝ)^3433 := by
    have hnat : (226830767 : ℕ)^4457*800000000000^3433 ≤ 286702497477^3433*500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226830767 500000000 286702497477 800000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267806943/625000000 : ℝ), (2022739909/5000000000 : ℝ), (226830767/500000000 : ℝ)] ![(2079873522549/6250000000000 : ℝ), (30884211447367/100000000000000 : ℝ), (286702497477/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267806943/625000000 : ℝ)|^4457 ≤ (2079873522549/6250000000000 : ℝ)^3433
        have hw : |(267806943/625000000 : ℝ)|=(267806943/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022739909/5000000000 : ℝ)|^4457 ≤ (30884211447367/100000000000000 : ℝ)^3433
        have hw : |(2022739909/5000000000 : ℝ)|=(2022739909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226830767/500000000 : ℝ)|^4457 ≤ (286702497477/800000000000 : ℝ)^3433
        have hw : |(226830767/500000000 : ℝ)|=(226830767/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29943401/156250000 : ℝ)*x 0 + (5216984239/10000000000 : ℝ)*x 1 + (1359071369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29943401/156250000 : ℝ)^4457 ≤ (11707349083859/100000000000000 : ℝ)^3433 := by
    have hnat : (29943401 : ℕ)^4457*100000000000000^3433 ≤ 11707349083859^3433*156250000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29943401 156250000 11707349083859 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216984239/10000000000 : ℝ)^4457 ≤ (42966603948023/100000000000000 : ℝ)^3433 := by
    have hnat : (5216984239 : ℕ)^4457*100000000000000^3433 ≤ 42966603948023^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216984239 10000000000 42966603948023 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359071369/2500000000 : ℝ)^4457 ≤ (22663023476789/50000000000000 : ℝ)^3433 := by
    have hnat : (1359071369 : ℕ)^4457*50000000000000^3433 ≤ 22663023476789^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359071369 2500000000 22663023476789 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29943401/156250000 : ℝ), (5216984239/10000000000 : ℝ), (1359071369/2500000000 : ℝ)] ![(11707349083859/100000000000000 : ℝ), (42966603948023/100000000000000 : ℝ), (22663023476789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29943401/156250000 : ℝ)|^4457 ≤ (11707349083859/100000000000000 : ℝ)^3433
        have hw : |(-29943401/156250000 : ℝ)|=(29943401/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216984239/10000000000 : ℝ)|^4457 ≤ (42966603948023/100000000000000 : ℝ)^3433
        have hw : |(5216984239/10000000000 : ℝ)|=(5216984239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359071369/2500000000 : ℝ)|^4457 ≤ (22663023476789/50000000000000 : ℝ)^3433
        have hw : |(1359071369/2500000000 : ℝ)|=(1359071369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295440919/10000000000 : ℝ)*x 0 + (-361893829/2000000000 : ℝ)*x 1 + (5436285757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295440919/10000000000 : ℝ)^4457 ≤ (5475922381851/12500000000000 : ℝ)^3433 := by
    have hnat : (5295440919 : ℕ)^4457*12500000000000^3433 ≤ 5475922381851^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295440919 10000000000 5475922381851 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361893829/2000000000 : ℝ)^4457 ≤ (5433285463761/50000000000000 : ℝ)^3433 := by
    have hnat : (361893829 : ℕ)^4457*50000000000000^3433 ≤ 5433285463761^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361893829 2000000000 5433285463761 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436285757/10000000000 : ℝ)^4457 ≤ (45326049995309/100000000000000 : ℝ)^3433 := by
    have hnat : (5436285757 : ℕ)^4457*100000000000000^3433 ≤ 45326049995309^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436285757 10000000000 45326049995309 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295440919/10000000000 : ℝ), (-361893829/2000000000 : ℝ), (5436285757/10000000000 : ℝ)] ![(5475922381851/12500000000000 : ℝ), (5433285463761/50000000000000 : ℝ), (45326049995309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295440919/10000000000 : ℝ)|^4457 ≤ (5475922381851/12500000000000 : ℝ)^3433
        have hw : |(5295440919/10000000000 : ℝ)|=(5295440919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-361893829/2000000000 : ℝ)|^4457 ≤ (5433285463761/50000000000000 : ℝ)^3433
        have hw : |(-361893829/2000000000 : ℝ)|=(361893829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436285757/10000000000 : ℝ)|^4457 ≤ (45326049995309/100000000000000 : ℝ)^3433
        have hw : |(5436285757/10000000000 : ℝ)|=(5436285757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059088171/2000000000 : ℝ)*x 0 + (543628557/1000000000 : ℝ)*x 1 + (-904734747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059088171/2000000000 : ℝ)^4457 ≤ (43807378367433/100000000000000 : ℝ)^3433 := by
    have hnat : (1059088171 : ℕ)^4457*100000000000000^3433 ≤ 43807378367433^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059088171 2000000000 43807378367433 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543628557/1000000000 : ℝ)^4457 ≤ (45326047971097/100000000000000 : ℝ)^3433 := by
    have hnat : (543628557 : ℕ)^4457*100000000000000^3433 ≤ 45326047971097^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543628557 1000000000 45326047971097 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904734747/5000000000 : ℝ)^4457 ≤ (5433286824283/50000000000000 : ℝ)^3433 := by
    have hnat : (904734747 : ℕ)^4457*50000000000000^3433 ≤ 5433286824283^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904734747 5000000000 5433286824283 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059088171/2000000000 : ℝ), (543628557/1000000000 : ℝ), (-904734747/5000000000 : ℝ)] ![(43807378367433/100000000000000 : ℝ), (45326047971097/100000000000000 : ℝ), (5433286824283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059088171/2000000000 : ℝ)|^4457 ≤ (43807378367433/100000000000000 : ℝ)^3433
        have hw : |(1059088171/2000000000 : ℝ)|=(1059088171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543628557/1000000000 : ℝ)|^4457 ≤ (45326047971097/100000000000000 : ℝ)^3433
        have hw : |(543628557/1000000000 : ℝ)|=(543628557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-904734747/5000000000 : ℝ)|^4457 ≤ (5433286824283/50000000000000 : ℝ)^3433
        have hw : |(-904734747/5000000000 : ℝ)|=(904734747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_s6_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284978121/10000000000 : ℝ)*x 0 + (4534102701/10000000000 : ℝ)*x 1 + (4048011173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284978121/10000000000 : ℝ)^4457 ≤ (1039957882719/3125000000000 : ℝ)^3433 := by
    have hnat : (4284978121 : ℕ)^4457*3125000000000^3433 ≤ 1039957882719^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284978121 10000000000 1039957882719 3125000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534102701/10000000000 : ℝ)^4457 ≤ (35812044667153/100000000000000 : ℝ)^3433 := by
    have hnat : (4534102701 : ℕ)^4457*100000000000000^3433 ≤ 35812044667153^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534102701 10000000000 35812044667153 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4048011173/10000000000 : ℝ)^4457 ≤ (1931831442373/6250000000000 : ℝ)^3433 := by
    have hnat : (4048011173 : ℕ)^4457*6250000000000^3433 ≤ 1931831442373^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048011173 10000000000 1931831442373 6250000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284978121/10000000000 : ℝ), (4534102701/10000000000 : ℝ), (4048011173/10000000000 : ℝ)] ![(1039957882719/3125000000000 : ℝ), (35812044667153/100000000000000 : ℝ), (1931831442373/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284978121/10000000000 : ℝ)|^4457 ≤ (1039957882719/3125000000000 : ℝ)^3433
        have hw : |(4284978121/10000000000 : ℝ)|=(4284978121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534102701/10000000000 : ℝ)|^4457 ≤ (35812044667153/100000000000000 : ℝ)^3433
        have hw : |(4534102701/10000000000 : ℝ)|=(4534102701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4048011173/10000000000 : ℝ)|^4457 ≤ (1931831442373/6250000000000 : ℝ)^3433
        have hw : |(4048011173/10000000000 : ℝ)|=(4048011173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5393/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (619/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2157/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2157/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2157/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2157/20000 : ℝ) ^ (4455/1024 : ℝ) ≤ (6197277497277859/100000000000000000000 : ℝ) := by
    have hpowers : (2157/20000 : ℝ)^4455 ≤ (6197277497277859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2157 : ℕ)^4455*100000000000000000000^1024 ≤ 6197277497277859^1024*20000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2157 20000 6197277497277859 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2157/20000 : ℝ)) (X := (6197277497277859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15477/100000 : ℝ) ^ (4455/1024 : ℝ) ≤ (29830649641469469/100000000000000000000 : ℝ) := by
    have hpowers : (15477/100000 : ℝ)^4455 ≤ (29830649641469469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15477 : ℕ)^4455*100000000000000000000^1024 ≤ 29830649641469469^1024*100000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15477 100000 29830649641469469 100000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15477/100000 : ℝ)) (X := (29830649641469469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006197277497277859/50000000000000000000 : ℝ) ≤ (250007122008189/250000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50006197277497277859/50000000000000000000 : ℝ)^1024 ≤ (250007122008189/250000000000000 : ℝ)^4455 := by
      have hnat : (50006197277497277859 : ℕ)^1024*250000000000000^4455 ≤ 250007122008189^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006197277497277859 50000000000000000000 250007122008189 250000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250007122008189/250000000000000 : ℝ)) (X := (50006197277497277859/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563062936361542927/1562500000000000000 : ℝ) ≤ (10000828001800843/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (1563062936361542927/1562500000000000000 : ℝ)^1024 ≤ (10000828001800843/10000000000000000 : ℝ)^4455 := by
      have hnat : (1563062936361542927 : ℕ)^1024*10000000000000000^4455 ≤ 10000828001800843^4455*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563062936361542927 1562500000000000000 10000828001800843 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000828001800843/10000000000000000 : ℝ)) (X := (1563062936361542927/1562500000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029830649641469469/50000000000000000000 : ℝ) ≤ (5000685561637063/5000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (50029830649641469469/50000000000000000000 : ℝ)^1024 ≤ (5000685561637063/5000000000000000 : ℝ)^4455 := by
      have hnat : (50029830649641469469 : ℕ)^1024*5000000000000000^4455 ≤ 5000685561637063^4455*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029830649641469469 50000000000000000000 5000685561637063 5000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000685561637063/5000000000000000 : ℝ)) (X := (50029830649641469469/50000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6197277497277859/100000000000000000000 : ℝ) ≤ ((1563654050943939907/1564000000000000000 : ℝ)+2*(543121473283/469200000000000 : ℝ)*(2157/20000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (1563654050943939907/1564000000000000000 : ℝ)+2*(543121473283/469200000000000 : ℝ)*(2157/20000 : ℝ)=(250007122008189/250000000000000 : ℝ) by norm_num, show 1+2*(6197277497277859/100000000000000000000 : ℝ)=(50006197277497277859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29830649641469469/100000000000000000000 : ℝ)+(6197277497277859/100000000000000000000 : ℝ) ≤ ((1563654050943939907/1564000000000000000 : ℝ)+(543121473283/469200000000000 : ℝ)*((15477/100000 : ℝ)+(2157/20000 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (1563654050943939907/1564000000000000000 : ℝ)+(543121473283/469200000000000 : ℝ)*((15477/100000 : ℝ)+(2157/20000 : ℝ))=(10000828001800843/10000000000000000 : ℝ) by norm_num, show 1+(29830649641469469/100000000000000000000 : ℝ)+(6197277497277859/100000000000000000000 : ℝ)=(1563062936361542927/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29830649641469469/100000000000000000000 : ℝ) ≤ ((1563654050943939907/1564000000000000000 : ℝ)+2*(543121473283/469200000000000 : ℝ)*(15477/100000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (1563654050943939907/1564000000000000000 : ℝ)+2*(543121473283/469200000000000 : ℝ)*(15477/100000 : ℝ)=(5000685561637063/5000000000000000 : ℝ) by norm_num, show 1+2*(29830649641469469/100000000000000000000 : ℝ)=(50029830649641469469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1563654050943939907/1564000000000000000 : ℝ)*(X 1 0+X 2 0)+(543121473283/469200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (1563654050943939907/1564000000000000000 : ℝ)) (alpha := (543121473283/469200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1563654050943939907/1564000000000000000 : ℝ)*(X 0 1+X 2 1)+(543121473283/469200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (1563654050943939907/1564000000000000000 : ℝ)) (alpha := (543121473283/469200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1563654050943939907/1564000000000000000 : ℝ)*(X 0 2+X 1 2)+(543121473283/469200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (2157/20000 : ℝ)) (hi := (15477/100000 : ℝ)) (c := (1563654050943939907/1564000000000000000 : ℝ)) (alpha := (543121473283/469200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-239543411/1250000000 : ℝ)*X 0 0+(1359356861/2500000000 : ℝ)*X 0 1+(5215850617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669163581/1250000000 : ℝ)*X 1 0+(-1014952177/5000000000 : ℝ)*X 1 1+(2607925269/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214132337/400000000 : ℝ)*X 2 0+(651981379/1250000000 : ℝ)*X 2 1+(-1014951999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((267806943/625000000 : ℝ)*X 0 0+(2022739909/5000000000 : ℝ)*X 0 1+(226830767/500000000 : ℝ)*X 0 2+(267806943/625000000 : ℝ)*X 1 0+(2022739909/5000000000 : ℝ)*X 1 1+(226830767/500000000 : ℝ)*X 1 2+(267806943/625000000 : ℝ)*X 2 0+(2022739909/5000000000 : ℝ)*X 2 1+(226830767/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-29943401/156250000 : ℝ)*X 0 0+(5216984239/10000000000 : ℝ)*X 0 1+(1359071369/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295440919/10000000000 : ℝ)*X 1 0+(-361893829/2000000000 : ℝ)*X 1 1+(5436285757/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059088171/2000000000 : ℝ)*X 2 0+(543628557/1000000000 : ℝ)*X 2 1+(-904734747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284978121/10000000000 : ℝ)*X 0 0+(4534102701/10000000000 : ℝ)*X 0 1+(4048011173/10000000000 : ℝ)*X 0 2+(4284978121/10000000000 : ℝ)*X 1 0+(4534102701/10000000000 : ℝ)*X 1 1+(4048011173/10000000000 : ℝ)*X 1 2+(4284978121/10000000000 : ℝ)*X 2 0+(4534102701/10000000000 : ℝ)*X 2 1+(4048011173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136571952010510751718661089/19550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (751402701/50000000000000 : ℝ)*(base19) + (284031501/25000000000000 : ℝ)*(base23) + (11956431/12500000000000 : ℝ)*(lower2) + (83313901/100000000000000 : ℝ)*(upper3) + (253772651/100000000000000 : ℝ)*(upper5) + (818659313558391/25000000000000 : ℝ)*(major0) + (818659313558391/25000000000000 : ℝ)*(major1) + (818659313558391/25000000000000 : ℝ)*(major2) + (112828217791637/2500000000000 : ℝ)*(sp0) + (564144303454673/12500000000000 : ℝ)*(sp1) + (2256577397158391/50000000000000 : ℝ)*(sp2) + (2036108926598613/100000000000000 : ℝ)*(sp3) + (13609388653/50000000000000 : ℝ)*(sp4) + (9418566467/100000000000000 : ℝ)*(sp7) + (50902958629127/2500000000000 : ℝ)*(f.failure) + (2256577965221393/50000000000000 : ℝ)*(f.sum) + (7660953389883/977500000000000000000000000 : ℝ)*base65 + (11518900531070419/1700000000000000000000000000000 : ℝ)*base67 + (1763428921329581/1700000000000000000000000000000 : ℝ)*base70 + (12997810043470419/1700000000000000000000000000000 : ℝ)*base71 + (869838459119/488750000000000000000000000 : ℝ)*base73 + (16318614659470419/1700000000000000000000000000000 : ℝ)*base75 + (24516684462870419/1700000000000000000000000000000 : ℝ)*base77 + (7142519277929581/1700000000000000000000000000000 : ℝ)*base80 + (2386462906287/977500000000000000000000000 : ℝ)*base82 + (401399/62500000000000000000 : ℝ)*base90 + (401399/62500000000000000000 : ℝ)*base92 + (401399/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17824761481579113366792249/7820000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (460880421/100000000000000 : ℝ)*(base19) + (316365581/100000000000000 : ℝ)*(base23) + (126254937/100000000000000 : ℝ)*(lower1) + (6297697/50000000000000 : ℝ)*(upper3) + (5059063/100000000000000 : ℝ)*(lower4) + (86152773/100000000000000 : ℝ)*(upper5) + (330857759129477/10000000000000 : ℝ)*(major0) + (330857759129477/10000000000000 : ℝ)*(major1) + (330857759129477/10000000000000 : ℝ)*(major2) + (9055560481/100000000000000 : ℝ)*(sp1) + (4559933189486971/100000000000000 : ℝ)*(sp4) + (1139980918261517/25000000000000 : ℝ)*(sp5) + (4559932873121389/100000000000000 : ℝ)*(sp6) + (411444383424637/20000000000000 : ℝ)*(sp7) + (411444383424637/20000000000000 : ℝ)*(f.failure) + (4559933189486971/100000000000000 : ℝ)*(f.sum) + (2116666157041/469200000000000000000000000 : ℝ)*base65 + (21928424598836779/2040000000000000000000000000000 : ℝ)*base67 + (14294731446956779/2040000000000000000000000000000 : ℝ)*base69 + (10386800624396779/2040000000000000000000000000000 : ℝ)*base71 + (890648006869/469200000000000000000000000 : ℝ)*base73 + (25208508968636779/2040000000000000000000000000000 : ℝ)*base75 + (3448043737796779/2040000000000000000000000000000 : ℝ)*base77 + (22588963010396779/2040000000000000000000000000000 : ℝ)*base79 + (22783658746697/2346000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (683731/500000000000000000000 : ℝ)*base89 + (683731/500000000000000000000 : ℝ)*base91 + (683731/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1480_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5393/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (619/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1480_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1480_box_0 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-169681701/1000000000 : ℝ)*x 0 + (5406299963/10000000000 : ℝ)*x 1 + (5406300241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169681701/1000000000 : ℝ)^4457 ≤ (9996534555559/100000000000000 : ℝ)^3433 := by
    have hnat : (169681701 : ℕ)^4457*100000000000000^3433 ≤ 9996534555559^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169681701 1000000000 9996534555559 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406299963/10000000000 : ℝ)^4457 ≤ (5625216401427/12500000000000 : ℝ)^3433 := by
    have hnat : (5406299963 : ℕ)^4457*12500000000000^3433 ≤ 5625216401427^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406299963 10000000000 5625216401427 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406300241/10000000000 : ℝ)^4457 ≤ (1406304194241/3125000000000 : ℝ)^3433 := by
    have hnat : (5406300241 : ℕ)^4457*3125000000000^3433 ≤ 1406304194241^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406300241 10000000000 1406304194241 3125000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169681701/1000000000 : ℝ), (5406299963/10000000000 : ℝ), (5406300241/10000000000 : ℝ)] ![(9996534555559/100000000000000 : ℝ), (5625216401427/12500000000000 : ℝ), (1406304194241/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169681701/1000000000 : ℝ)|^4457 ≤ (9996534555559/100000000000000 : ℝ)^3433
        have hw : |(-169681701/1000000000 : ℝ)|=(169681701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406299963/10000000000 : ℝ)|^4457 ≤ (5625216401427/12500000000000 : ℝ)^3433
        have hw : |(5406299963/10000000000 : ℝ)|=(5406299963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406300241/10000000000 : ℝ)|^4457 ≤ (1406304194241/3125000000000 : ℝ)^3433
        have hw : |(5406300241/10000000000 : ℝ)|=(5406300241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_1 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658779123/1250000000 : ℝ)*x 0 + (-942648503/5000000000 : ℝ)*x 1 + (5406299967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658779123/1250000000 : ℝ)^4457 ≤ (43536832217773/100000000000000 : ℝ)^3433 := by
    have hnat : (658779123 : ℕ)^4457*100000000000000^3433 ≤ 43536832217773^3433*1250000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658779123 1250000000 43536832217773 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942648503/5000000000 : ℝ)^4457 ≤ (2865359129181/25000000000000 : ℝ)^3433 := by
    have hnat : (942648503 : ℕ)^4457*25000000000000^3433 ≤ 2865359129181^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942648503 5000000000 2865359129181 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406299967/10000000000 : ℝ)^4457 ≤ (45001731254643/100000000000000 : ℝ)^3433 := by
    have hnat : (5406299967 : ℕ)^4457*100000000000000^3433 ≤ 45001731254643^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406299967 10000000000 45001731254643 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658779123/1250000000 : ℝ), (-942648503/5000000000 : ℝ), (5406299967/10000000000 : ℝ)] ![(43536832217773/100000000000000 : ℝ), (2865359129181/25000000000000 : ℝ), (45001731254643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658779123/1250000000 : ℝ)|^4457 ≤ (43536832217773/100000000000000 : ℝ)^3433
        have hw : |(658779123/1250000000 : ℝ)|=(658779123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942648503/5000000000 : ℝ)|^4457 ≤ (2865359129181/25000000000000 : ℝ)^3433
        have hw : |(-942648503/5000000000 : ℝ)|=(942648503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406299967/10000000000 : ℝ)|^4457 ≤ (45001731254643/100000000000000 : ℝ)^3433
        have hw : |(5406299967/10000000000 : ℝ)|=(5406299967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_2 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270232607/10000000000 : ℝ)*x 0 + (2703150061/5000000000 : ℝ)*x 1 + (-377059461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270232607/10000000000 : ℝ)^4457 ≤ (21768414087231/50000000000000 : ℝ)^3433 := by
    have hnat : (5270232607 : ℕ)^4457*50000000000000^3433 ≤ 21768414087231^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270232607 10000000000 21768414087231 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703150061/5000000000 : ℝ)^4457 ≤ (450017329297/1000000000000 : ℝ)^3433 := by
    have hnat : (2703150061 : ℕ)^4457*1000000000000^3433 ≤ 450017329297^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703150061 5000000000 450017329297 1000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377059461/2000000000 : ℝ)^4457 ≤ (2292287775331/20000000000000 : ℝ)^3433 := by
    have hnat : (377059461 : ℕ)^4457*20000000000000^3433 ≤ 2292287775331^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377059461 2000000000 2292287775331 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270232607/10000000000 : ℝ), (2703150061/5000000000 : ℝ), (-377059461/2000000000 : ℝ)] ![(21768414087231/50000000000000 : ℝ), (450017329297/1000000000000 : ℝ), (2292287775331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270232607/10000000000 : ℝ)|^4457 ≤ (21768414087231/50000000000000 : ℝ)^3433
        have hw : |(5270232607/10000000000 : ℝ)|=(5270232607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703150061/5000000000 : ℝ)|^4457 ≤ (450017329297/1000000000000 : ℝ)^3433
        have hw : |(2703150061/5000000000 : ℝ)|=(2703150061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-377059461/2000000000 : ℝ)|^4457 ≤ (2292287775331/20000000000000 : ℝ)^3433
        have hw : |(-377059461/2000000000 : ℝ)|=(377059461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_3 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2244756433/5000000000 : ℝ)*x 0 + (261863047/625000000 : ℝ)*x 1 + (2094904127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244756433/5000000000 : ℝ)^4457 ≤ (35355478694927/100000000000000 : ℝ)^3433 := by
    have hnat : (2244756433 : ℕ)^4457*100000000000000^3433 ≤ 35355478694927^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244756433 5000000000 35355478694927 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261863047/625000000 : ℝ)^4457 ≤ (32322263142657/100000000000000 : ℝ)^3433 := by
    have hnat : (261863047 : ℕ)^4457*100000000000000^3433 ≤ 32322263142657^3433*625000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261863047 625000000 32322263142657 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2094904127/5000000000 : ℝ)^4457 ≤ (6464451630979/20000000000000 : ℝ)^3433 := by
    have hnat : (2094904127 : ℕ)^4457*20000000000000^3433 ≤ 6464451630979^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094904127 5000000000 6464451630979 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2244756433/5000000000 : ℝ), (261863047/625000000 : ℝ), (2094904127/5000000000 : ℝ)] ![(35355478694927/100000000000000 : ℝ), (32322263142657/100000000000000 : ℝ), (6464451630979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2244756433/5000000000 : ℝ)|^4457 ≤ (35355478694927/100000000000000 : ℝ)^3433
        have hw : |(2244756433/5000000000 : ℝ)|=(2244756433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261863047/625000000 : ℝ)|^4457 ≤ (32322263142657/100000000000000 : ℝ)^3433
        have hw : |(261863047/625000000 : ℝ)|=(261863047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2094904127/5000000000 : ℝ)|^4457 ≤ (6464451630979/20000000000000 : ℝ)^3433
        have hw : |(2094904127/5000000000 : ℝ)|=(2094904127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_4 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141348863/10000000000 : ℝ)*x 0 + (2621218193/5000000000 : ℝ)*x 1 + (81913079/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141348863/10000000000 : ℝ)^4457 ≤ (1690261727793/12500000000000 : ℝ)^3433 := by
    have hnat : (2141348863 : ℕ)^4457*12500000000000^3433 ≤ 1690261727793^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141348863 10000000000 1690261727793 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621218193/5000000000 : ℝ)^4457 ≤ (21619474748473/50000000000000 : ℝ)^3433 := by
    have hnat : (2621218193 : ℕ)^4457*50000000000000^3433 ≤ 21619474748473^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621218193 5000000000 21619474748473 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81913079/156250000 : ℝ)^4457 ≤ (21619478335673/50000000000000 : ℝ)^3433 := by
    have hnat : (81913079 : ℕ)^4457*50000000000000^3433 ≤ 21619478335673^3433*156250000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81913079 156250000 21619478335673 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141348863/10000000000 : ℝ), (2621218193/5000000000 : ℝ), (81913079/156250000 : ℝ)] ![(1690261727793/12500000000000 : ℝ), (21619474748473/50000000000000 : ℝ), (21619478335673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141348863/10000000000 : ℝ)|^4457 ≤ (1690261727793/12500000000000 : ℝ)^3433
        have hw : |(-2141348863/10000000000 : ℝ)|=(2141348863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621218193/5000000000 : ℝ)|^4457 ≤ (21619474748473/50000000000000 : ℝ)^3433
        have hw : |(2621218193/5000000000 : ℝ)|=(2621218193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81913079/156250000 : ℝ)|^4457 ≤ (21619478335673/50000000000000 : ℝ)^3433
        have hw : |(81913079/156250000 : ℝ)|=(81913079/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_5 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215384143/400000000 : ℝ)*x 0 + (-1952373371/10000000000 : ℝ)*x 1 + (524243717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215384143/400000000 : ℝ)^4457 ≤ (22383701360907/50000000000000 : ℝ)^3433 := by
    have hnat : (215384143 : ℕ)^4457*50000000000000^3433 ≤ 22383701360907^3433*400000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215384143 400000000 22383701360907 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952373371/10000000000 : ℝ)^4457 ≤ (11993639377389/100000000000000 : ℝ)^3433 := by
    have hnat : (1952373371 : ℕ)^4457*100000000000000^3433 ≤ 11993639377389^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952373371 10000000000 11993639377389 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524243717/1000000000 : ℝ)^4457 ≤ (8647791578413/20000000000000 : ℝ)^3433 := by
    have hnat : (524243717 : ℕ)^4457*20000000000000^3433 ≤ 8647791578413^3433*1000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524243717 1000000000 8647791578413 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215384143/400000000 : ℝ), (-1952373371/10000000000 : ℝ), (524243717/1000000000 : ℝ)] ![(22383701360907/50000000000000 : ℝ), (11993639377389/100000000000000 : ℝ), (8647791578413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215384143/400000000 : ℝ)|^4457 ≤ (22383701360907/50000000000000 : ℝ)^3433
        have hw : |(215384143/400000000 : ℝ)|=(215384143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952373371/10000000000 : ℝ)|^4457 ≤ (11993639377389/100000000000000 : ℝ)^3433
        have hw : |(-1952373371/10000000000 : ℝ)|=(1952373371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524243717/1000000000 : ℝ)|^4457 ≤ (8647791578413/20000000000000 : ℝ)^3433
        have hw : |(524243717/1000000000 : ℝ)|=(524243717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_6 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076920793/2000000000 : ℝ)*x 0 + (5242436709/10000000000 : ℝ)*x 1 + (-976186731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076920793/2000000000 : ℝ)^4457 ≤ (44767406931421/100000000000000 : ℝ)^3433 := by
    have hnat : (1076920793 : ℕ)^4457*100000000000000^3433 ≤ 44767406931421^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076920793 2000000000 44767406931421 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242436709/10000000000 : ℝ)^4457 ≤ (43238952955649/100000000000000 : ℝ)^3433 := by
    have hnat : (5242436709 : ℕ)^4457*100000000000000^3433 ≤ 43238952955649^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242436709 10000000000 43238952955649 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976186731/5000000000 : ℝ)^4457 ≤ (5996820051579/50000000000000 : ℝ)^3433 := by
    have hnat : (976186731 : ℕ)^4457*50000000000000^3433 ≤ 5996820051579^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976186731 5000000000 5996820051579 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076920793/2000000000 : ℝ), (5242436709/10000000000 : ℝ), (-976186731/5000000000 : ℝ)] ![(44767406931421/100000000000000 : ℝ), (43238952955649/100000000000000 : ℝ), (5996820051579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076920793/2000000000 : ℝ)|^4457 ≤ (44767406931421/100000000000000 : ℝ)^3433
        have hw : |(1076920793/2000000000 : ℝ)|=(1076920793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242436709/10000000000 : ℝ)|^4457 ≤ (43238952955649/100000000000000 : ℝ)^3433
        have hw : |(5242436709/10000000000 : ℝ)|=(5242436709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-976186731/5000000000 : ℝ)|^4457 ≤ (5996820051579/50000000000000 : ℝ)^3433
        have hw : |(-976186731/5000000000 : ℝ)|=(976186731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_7 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4078051283/10000000000 : ℝ)*x 0 + (4395400597/10000000000 : ℝ)*x 1 + (2197700343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4078051283/10000000000 : ℝ)^4457 ≤ (15603713705817/50000000000000 : ℝ)^3433 := by
    have hnat : (4078051283 : ℕ)^4457*50000000000000^3433 ≤ 15603713705817^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4078051283 10000000000 15603713705817 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4395400597/10000000000 : ℝ)^4457 ≤ (4299535729617/12500000000000 : ℝ)^3433 := by
    have hnat : (4395400597 : ℕ)^4457*12500000000000^3433 ≤ 4299535729617^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395400597 10000000000 4299535729617 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197700343/5000000000 : ℝ)^4457 ≤ (34396286741151/100000000000000 : ℝ)^3433 := by
    have hnat : (2197700343 : ℕ)^4457*100000000000000^3433 ≤ 34396286741151^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197700343 5000000000 34396286741151 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4078051283/10000000000 : ℝ), (4395400597/10000000000 : ℝ), (2197700343/5000000000 : ℝ)] ![(15603713705817/50000000000000 : ℝ), (4299535729617/12500000000000 : ℝ), (34396286741151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4078051283/10000000000 : ℝ)|^4457 ≤ (15603713705817/50000000000000 : ℝ)^3433
        have hw : |(4078051283/10000000000 : ℝ)|=(4078051283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4395400597/10000000000 : ℝ)|^4457 ≤ (4299535729617/12500000000000 : ℝ)^3433
        have hw : |(4395400597/10000000000 : ℝ)|=(4395400597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2197700343/5000000000 : ℝ)|^4457 ≤ (34396286741151/100000000000000 : ℝ)^3433
        have hw : |(2197700343/5000000000 : ℝ)|=(2197700343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_8 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047592727/10000000000 : ℝ)*x 0 + (320500137/625000000 : ℝ)*x 1 + (1356711337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047592727/10000000000 : ℝ)^4457 ≤ (2551704347047/20000000000000 : ℝ)^3433 := by
    have hnat : (2047592727 : ℕ)^4457*20000000000000^3433 ≤ 2551704347047^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047592727 10000000000 2551704347047 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320500137/625000000 : ℝ)^4457 ≤ (5252198879841/12500000000000 : ℝ)^3433 := by
    have hnat : (320500137 : ℕ)^4457*12500000000000^3433 ≤ 5252198879841^3433*625000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320500137 625000000 5252198879841 12500000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356711337/2500000000 : ℝ)^4457 ≤ (9044777443237/20000000000000 : ℝ)^3433 := by
    have hnat : (1356711337 : ℕ)^4457*20000000000000^3433 ≤ 9044777443237^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356711337 2500000000 9044777443237 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047592727/10000000000 : ℝ), (320500137/625000000 : ℝ), (1356711337/2500000000 : ℝ)] ![(2551704347047/20000000000000 : ℝ), (5252198879841/12500000000000 : ℝ), (9044777443237/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047592727/10000000000 : ℝ)|^4457 ≤ (2551704347047/20000000000000 : ℝ)^3433
        have hw : |(-2047592727/10000000000 : ℝ)|=(2047592727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320500137/625000000 : ℝ)|^4457 ≤ (5252198879841/12500000000000 : ℝ)^3433
        have hw : |(320500137/625000000 : ℝ)|=(320500137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356711337/2500000000 : ℝ)|^4457 ≤ (9044777443237/20000000000000 : ℝ)^3433
        have hw : |(1356711337/2500000000 : ℝ)|=(1356711337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_9 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313971257/2500000000 : ℝ)*x 0 + (-938316159/5000000000 : ℝ)*x 1 + (217073829/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313971257/2500000000 : ℝ)^4457 ≤ (21691506713279/50000000000000 : ℝ)^3433 := by
    have hnat : (1313971257 : ℕ)^4457*50000000000000^3433 ≤ 21691506713279^3433*2500000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313971257 2500000000 21691506713279 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938316159/5000000000 : ℝ)^4457 ≤ (2278619052981/20000000000000 : ℝ)^3433 := by
    have hnat : (938316159 : ℕ)^4457*20000000000000^3433 ≤ 2278619052981^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938316159 5000000000 2278619052981 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217073829/400000000 : ℝ)^4457 ≤ (45223891294969/100000000000000 : ℝ)^3433 := by
    have hnat : (217073829 : ℕ)^4457*100000000000000^3433 ≤ 45223891294969^3433*400000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217073829 400000000 45223891294969 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313971257/2500000000 : ℝ), (-938316159/5000000000 : ℝ), (217073829/400000000 : ℝ)] ![(21691506713279/50000000000000 : ℝ), (2278619052981/20000000000000 : ℝ), (45223891294969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313971257/2500000000 : ℝ)|^4457 ≤ (21691506713279/50000000000000 : ℝ)^3433
        have hw : |(1313971257/2500000000 : ℝ)|=(1313971257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-938316159/5000000000 : ℝ)|^4457 ≤ (2278619052981/20000000000000 : ℝ)^3433
        have hw : |(-938316159/5000000000 : ℝ)|=(938316159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217073829/400000000 : ℝ)|^4457 ≤ (45223891294969/100000000000000 : ℝ)^3433
        have hw : |(217073829/400000000 : ℝ)|=(217073829/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_10 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255885367/10000000000 : ℝ)*x 0 + (1085369027/2000000000 : ℝ)*x 1 + (-1876632667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255885367/10000000000 : ℝ)^4457 ≤ (21691508529683/50000000000000 : ℝ)^3433 := by
    have hnat : (5255885367 : ℕ)^4457*50000000000000^3433 ≤ 21691508529683^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255885367 10000000000 21691508529683 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085369027/2000000000 : ℝ)^4457 ≤ (45223884911727/100000000000000 : ℝ)^3433 := by
    have hnat : (1085369027 : ℕ)^4457*100000000000000^3433 ≤ 45223884911727^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085369027 2000000000 45223884911727 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876632667/10000000000 : ℝ)^4457 ≤ (11393098015691/100000000000000 : ℝ)^3433 := by
    have hnat : (1876632667 : ℕ)^4457*100000000000000^3433 ≤ 11393098015691^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876632667 10000000000 11393098015691 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255885367/10000000000 : ℝ), (1085369027/2000000000 : ℝ), (-1876632667/10000000000 : ℝ)] ![(21691508529683/50000000000000 : ℝ), (45223884911727/100000000000000 : ℝ), (11393098015691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255885367/10000000000 : ℝ)|^4457 ≤ (21691508529683/50000000000000 : ℝ)^3433
        have hw : |(5255885367/10000000000 : ℝ)|=(5255885367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085369027/2000000000 : ℝ)|^4457 ≤ (45223884911727/100000000000000 : ℝ)^3433
        have hw : |(1085369027/2000000000 : ℝ)|=(1085369027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876632667/10000000000 : ℝ)|^4457 ≤ (11393098015691/100000000000000 : ℝ)^3433
        have hw : |(-1876632667/10000000000 : ℝ)|=(1876632667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_11 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2269972983/5000000000 : ℝ)*x 0 + (4164000021/10000000000 : ℝ)*x 1 + (4164000259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2269972983/5000000000 : ℝ)^4457 ≤ (17935987426007/50000000000000 : ℝ)^3433 := by
    have hnat : (2269972983 : ℕ)^4457*50000000000000^3433 ≤ 17935987426007^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269972983 5000000000 17935987426007 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4164000021/10000000000 : ℝ)^4457 ≤ (8016002843901/25000000000000 : ℝ)^3433 := by
    have hnat : (4164000021 : ℕ)^4457*25000000000000^3433 ≤ 8016002843901^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164000021 10000000000 8016002843901 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4164000259/10000000000 : ℝ)^4457 ≤ (8016003438731/25000000000000 : ℝ)^3433 := by
    have hnat : (4164000259 : ℕ)^4457*25000000000000^3433 ≤ 8016003438731^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164000259 10000000000 8016003438731 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2269972983/5000000000 : ℝ), (4164000021/10000000000 : ℝ), (4164000259/10000000000 : ℝ)] ![(17935987426007/50000000000000 : ℝ), (8016002843901/25000000000000 : ℝ), (8016003438731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2269972983/5000000000 : ℝ)|^4457 ≤ (17935987426007/50000000000000 : ℝ)^3433
        have hw : |(2269972983/5000000000 : ℝ)|=(2269972983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4164000021/10000000000 : ℝ)|^4457 ≤ (8016002843901/25000000000000 : ℝ)^3433
        have hw : |(4164000021/10000000000 : ℝ)|=(4164000021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4164000259/10000000000 : ℝ)|^4457 ≤ (8016003438731/25000000000000 : ℝ)^3433
        have hw : |(4164000259/10000000000 : ℝ)|=(4164000259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_12 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-895352009/5000000000 : ℝ)*x 0 + (5516939219/10000000000 : ℝ)*x 1 + (5227444719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895352009/5000000000 : ℝ)^4457 ≤ (214409838409/2000000000000 : ℝ)^3433 := by
    have hnat : (895352009 : ℕ)^4457*2000000000000^3433 ≤ 214409838409^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895352009 5000000000 214409838409 2000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516939219/10000000000 : ℝ)^4457 ≤ (11550255432469/25000000000000 : ℝ)^3433 := by
    have hnat : (5516939219 : ℕ)^4457*25000000000000^3433 ≤ 11550255432469^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516939219 10000000000 11550255432469 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227444719/10000000000 : ℝ)^4457 ≤ (43078486339031/100000000000000 : ℝ)^3433 := by
    have hnat : (5227444719 : ℕ)^4457*100000000000000^3433 ≤ 43078486339031^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227444719 10000000000 43078486339031 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-895352009/5000000000 : ℝ), (5516939219/10000000000 : ℝ), (5227444719/10000000000 : ℝ)] ![(214409838409/2000000000000 : ℝ), (11550255432469/25000000000000 : ℝ), (43078486339031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-895352009/5000000000 : ℝ)|^4457 ≤ (214409838409/2000000000000 : ℝ)^3433
        have hw : |(-895352009/5000000000 : ℝ)|=(895352009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516939219/10000000000 : ℝ)|^4457 ≤ (11550255432469/25000000000000 : ℝ)^3433
        have hw : |(5516939219/10000000000 : ℝ)|=(5516939219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227444719/10000000000 : ℝ)|^4457 ≤ (43078486339031/100000000000000 : ℝ)^3433
        have hw : |(5227444719/10000000000 : ℝ)|=(5227444719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_13 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697533421/5000000000 : ℝ)*x 0 + (-39166527/200000000 : ℝ)*x 1 + (2613722373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697533421/5000000000 : ℝ)^4457 ≤ (44880374532141/100000000000000 : ℝ)^3433 := by
    have hnat : (2697533421 : ℕ)^4457*100000000000000^3433 ≤ 44880374532141^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697533421 5000000000 44880374532141 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39166527/200000000 : ℝ)^4457 ≤ (3010284707359/25000000000000 : ℝ)^3433 := by
    have hnat : (39166527 : ℕ)^4457*25000000000000^3433 ≤ 3010284707359^3433*200000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39166527 200000000 3010284707359 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613722373/5000000000 : ℝ)^4457 ≤ (21539243313951/50000000000000 : ℝ)^3433 := by
    have hnat : (2613722373 : ℕ)^4457*50000000000000^3433 ≤ 21539243313951^3433*5000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613722373 5000000000 21539243313951 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697533421/5000000000 : ℝ), (-39166527/200000000 : ℝ), (2613722373/5000000000 : ℝ)] ![(44880374532141/100000000000000 : ℝ), (3010284707359/25000000000000 : ℝ), (21539243313951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697533421/5000000000 : ℝ)|^4457 ≤ (44880374532141/100000000000000 : ℝ)^3433
        have hw : |(2697533421/5000000000 : ℝ)|=(2697533421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39166527/200000000 : ℝ)|^4457 ≤ (3010284707359/25000000000000 : ℝ)^3433
        have hw : |(-39166527/200000000 : ℝ)|=(39166527/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613722373/5000000000 : ℝ)|^4457 ≤ (21539243313951/50000000000000 : ℝ)^3433
        have hw : |(2613722373/5000000000 : ℝ)|=(2613722373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_14 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5395066829/10000000000 : ℝ)*x 0 + (1045488937/2000000000 : ℝ)*x 1 + (-1958326449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5395066829/10000000000 : ℝ)^4457 ≤ (44880374391739/100000000000000 : ℝ)^3433 := by
    have hnat : (5395066829 : ℕ)^4457*100000000000000^3433 ≤ 44880374391739^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395066829 10000000000 44880374391739 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045488937/2000000000 : ℝ)^4457 ≤ (10769621493817/25000000000000 : ℝ)^3433 := by
    have hnat : (1045488937 : ℕ)^4457*25000000000000^3433 ≤ 10769621493817^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045488937 2000000000 10769621493817 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958326449/10000000000 : ℝ)^4457 ≤ (6020569809863/50000000000000 : ℝ)^3433 := by
    have hnat : (1958326449 : ℕ)^4457*50000000000000^3433 ≤ 6020569809863^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958326449 10000000000 6020569809863 50000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5395066829/10000000000 : ℝ), (1045488937/2000000000 : ℝ), (-1958326449/10000000000 : ℝ)] ![(44880374391739/100000000000000 : ℝ), (10769621493817/25000000000000 : ℝ), (6020569809863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5395066829/10000000000 : ℝ)|^4457 ≤ (44880374391739/100000000000000 : ℝ)^3433
        have hw : |(5395066829/10000000000 : ℝ)|=(5395066829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045488937/2000000000 : ℝ)|^4457 ≤ (10769621493817/25000000000000 : ℝ)^3433
        have hw : |(1045488937/2000000000 : ℝ)|=(1045488937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958326449/10000000000 : ℝ)|^4457 ≤ (6020569809863/50000000000000 : ℝ)^3433
        have hw : |(-1958326449/10000000000 : ℝ)|=(1958326449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1480_box_15 (p : ℝ) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (252471497/625000000 : ℝ)*x 0 + (4414189129/10000000000 : ℝ)*x 1 + (882838239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252471497/625000000 : ℝ)^4457 ≤ (7706347885657/25000000000000 : ℝ)^3433 := by
    have hnat : (252471497 : ℕ)^4457*25000000000000^3433 ≤ 7706347885657^3433*625000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252471497 625000000 7706347885657 25000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414189129/10000000000 : ℝ)^4457 ≤ (34587293711021/100000000000000 : ℝ)^3433 := by
    have hnat : (4414189129 : ℕ)^4457*100000000000000^3433 ≤ 34587293711021^3433*10000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414189129 10000000000 34587293711021 100000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882838239/2000000000 : ℝ)^4457 ≤ (6917462945547/20000000000000 : ℝ)^3433 := by
    have hnat : (882838239 : ℕ)^4457*20000000000000^3433 ≤ 6917462945547^3433*2000000000^4457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882838239 2000000000 6917462945547 20000000000000 4457 3433 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4457/1024 : ℝ)) 4457 3433 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252471497/625000000 : ℝ), (4414189129/10000000000 : ℝ), (882838239/2000000000 : ℝ)] ![(7706347885657/25000000000000 : ℝ), (34587293711021/100000000000000 : ℝ), (6917462945547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252471497/625000000 : ℝ)|^4457 ≤ (7706347885657/25000000000000 : ℝ)^3433
        have hw : |(252471497/625000000 : ℝ)|=(252471497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414189129/10000000000 : ℝ)|^4457 ≤ (34587293711021/100000000000000 : ℝ)^3433
        have hw : |(4414189129/10000000000 : ℝ)|=(4414189129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882838239/2000000000 : ℝ)|^4457 ≤ (6917462945547/20000000000000 : ℝ)^3433
        have hw : |(882838239/2000000000 : ℝ)|=(882838239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1480_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5393/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31851/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29239/50000 : ℝ) ∧ (2499/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42897/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5393/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (619/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5393/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5393/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (619/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5393/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5393/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (619/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5393/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5393/50000 : ℝ) ^ (4455/1024 : ℝ) ≤ (3099888909823751/50000000000000000000 : ℝ) := by
    have hpowers : (5393/50000 : ℝ)^4455 ≤ (3099888909823751/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5393 : ℕ)^4455*50000000000000000000^1024 ≤ 3099888909823751^1024*50000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5393 50000 3099888909823751 50000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5393/50000 : ℝ)) (X := (3099888909823751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (619/4000 : ℝ) ^ (4455/1024 : ℝ) ≤ (1192555299031217/4000000000000000000 : ℝ) := by
    have hpowers : (619/4000 : ℝ)^4455 ≤ (1192555299031217/4000000000000000000 : ℝ)^1024 := by
      have hnat : (619 : ℕ)^4455*4000000000000000000^1024 ≤ 1192555299031217^1024*4000^4455 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        619 4000 1192555299031217 4000000000000000000 4455 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (619/4000 : ℝ)) (X := (1192555299031217/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003099888909823751/25000000000000000000 : ℝ) ≤ (2000056999051691/2000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (25003099888909823751/25000000000000000000 : ℝ)^1024 ≤ (2000056999051691/2000000000000000 : ℝ)^4455 := by
      have hnat : (25003099888909823751 : ℕ)^1024*2000000000000000^4455 ≤ 2000056999051691^4455*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003099888909823751 25000000000000000000 2000056999051691 2000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056999051691/2000000000000000 : ℝ)) (X := (25003099888909823751/25000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036013660295427927/100000000000000000000 : ℝ) ≤ (2500206918490637/2500000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (100036013660295427927/100000000000000000000 : ℝ)^1024 ≤ (2500206918490637/2500000000000000 : ℝ)^4455 := by
      have hnat : (100036013660295427927 : ℕ)^1024*2500000000000000^4455 ≤ 2500206918490637^4455*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036013660295427927 100000000000000000000 2500206918490637 2500000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500206918490637/2500000000000000 : ℝ)) (X := (100036013660295427927/100000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001192555299031217/2000000000000000000 : ℝ) ≤ (10001370352666641/10000000000000000 : ℝ) ^ (4455/1024 : ℝ) := by
    have hpowers : (2001192555299031217/2000000000000000000 : ℝ)^1024 ≤ (10001370352666641/10000000000000000 : ℝ)^4455 := by
      have hnat : (2001192555299031217 : ℕ)^1024*10000000000000000^4455 ≤ 10001370352666641^4455*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001192555299031217 2000000000000000000 10001370352666641 10000000000000000 1024 4455 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001370352666641/10000000000000000 : ℝ)) (X := (2001192555299031217/2000000000000000000 : ℝ)) (by norm_num) 4455 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3099888909823751/50000000000000000000 : ℝ) ≤ ((46879629677762201299/46890000000000000000 : ℝ)+2*(542678704093/468900000000000 : ℝ)*(5393/50000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (46879629677762201299/46890000000000000000 : ℝ)+2*(542678704093/468900000000000 : ℝ)*(5393/50000 : ℝ)=(2000056999051691/2000000000000000 : ℝ) by norm_num, show 1+2*(3099888909823751/50000000000000000000 : ℝ)=(25003099888909823751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1192555299031217/4000000000000000000 : ℝ)+(3099888909823751/50000000000000000000 : ℝ) ≤ ((46879629677762201299/46890000000000000000 : ℝ)+(542678704093/468900000000000 : ℝ)*((619/4000 : ℝ)+(5393/50000 : ℝ)))^(4455/1024 : ℝ) := by
    rw [show (46879629677762201299/46890000000000000000 : ℝ)+(542678704093/468900000000000 : ℝ)*((619/4000 : ℝ)+(5393/50000 : ℝ))=(2500206918490637/2500000000000000 : ℝ) by norm_num, show 1+(1192555299031217/4000000000000000000 : ℝ)+(3099888909823751/50000000000000000000 : ℝ)=(100036013660295427927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1192555299031217/4000000000000000000 : ℝ) ≤ ((46879629677762201299/46890000000000000000 : ℝ)+2*(542678704093/468900000000000 : ℝ)*(619/4000 : ℝ))^(4455/1024 : ℝ) := by
    rw [show (46879629677762201299/46890000000000000000 : ℝ)+2*(542678704093/468900000000000 : ℝ)*(619/4000 : ℝ)=(10001370352666641/10000000000000000 : ℝ) by norm_num, show 1+2*(1192555299031217/4000000000000000000 : ℝ)=(2001192555299031217/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46879629677762201299/46890000000000000000 : ℝ)*(X 1 0+X 2 0)+(542678704093/468900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (5393/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (46879629677762201299/46890000000000000000 : ℝ)) (alpha := (542678704093/468900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46879629677762201299/46890000000000000000 : ℝ)*(X 0 1+X 2 1)+(542678704093/468900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (5393/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (46879629677762201299/46890000000000000000 : ℝ)) (alpha := (542678704093/468900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46879629677762201299/46890000000000000000 : ℝ)*(X 0 2+X 1 2)+(542678704093/468900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4455/1024 : ℝ)) (lo := (5393/50000 : ℝ)) (hi := (619/4000 : ℝ)) (c := (46879629677762201299/46890000000000000000 : ℝ)) (alpha := (542678704093/468900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-169681701/1000000000 : ℝ)*X 0 0+(5406299963/10000000000 : ℝ)*X 0 1+(5406300241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((658779123/1250000000 : ℝ)*X 1 0+(-942648503/5000000000 : ℝ)*X 1 1+(5406299967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270232607/10000000000 : ℝ)*X 2 0+(2703150061/5000000000 : ℝ)*X 2 1+(-377059461/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2244756433/5000000000 : ℝ)*X 0 0+(261863047/625000000 : ℝ)*X 0 1+(2094904127/5000000000 : ℝ)*X 0 2+(2244756433/5000000000 : ℝ)*X 1 0+(261863047/625000000 : ℝ)*X 1 1+(2094904127/5000000000 : ℝ)*X 1 2+(2244756433/5000000000 : ℝ)*X 2 0+(261863047/625000000 : ℝ)*X 2 1+(2094904127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2141348863/10000000000 : ℝ)*X 0 0+(2621218193/5000000000 : ℝ)*X 0 1+(81913079/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((215384143/400000000 : ℝ)*X 1 0+(-1952373371/10000000000 : ℝ)*X 1 1+(524243717/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1076920793/2000000000 : ℝ)*X 2 0+(5242436709/10000000000 : ℝ)*X 2 1+(-976186731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4078051283/10000000000 : ℝ)*X 0 0+(4395400597/10000000000 : ℝ)*X 0 1+(2197700343/5000000000 : ℝ)*X 0 2+(4078051283/10000000000 : ℝ)*X 1 0+(4395400597/10000000000 : ℝ)*X 1 1+(2197700343/5000000000 : ℝ)*X 1 2+(4078051283/10000000000 : ℝ)*X 2 0+(4395400597/10000000000 : ℝ)*X 2 1+(2197700343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2047592727/10000000000 : ℝ)*X 0 0+(320500137/625000000 : ℝ)*X 0 1+(1356711337/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1313971257/2500000000 : ℝ)*X 1 0+(-938316159/5000000000 : ℝ)*X 1 1+(217073829/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5255885367/10000000000 : ℝ)*X 2 0+(1085369027/2000000000 : ℝ)*X 2 1+(-1876632667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2269972983/5000000000 : ℝ)*X 0 0+(4164000021/10000000000 : ℝ)*X 0 1+(4164000259/10000000000 : ℝ)*X 0 2+(2269972983/5000000000 : ℝ)*X 1 0+(4164000021/10000000000 : ℝ)*X 1 1+(4164000259/10000000000 : ℝ)*X 1 2+(2269972983/5000000000 : ℝ)*X 2 0+(4164000021/10000000000 : ℝ)*X 2 1+(4164000259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-895352009/5000000000 : ℝ)*X 0 0+(5516939219/10000000000 : ℝ)*X 0 1+(5227444719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2697533421/5000000000 : ℝ)*X 1 0+(-39166527/200000000 : ℝ)*X 1 1+(2613722373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5395066829/10000000000 : ℝ)*X 2 0+(1045488937/2000000000 : ℝ)*X 2 1+(-1958326449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((252471497/625000000 : ℝ)*X 0 0+(4414189129/10000000000 : ℝ)*X 0 1+(882838239/2000000000 : ℝ)*X 0 2+(252471497/625000000 : ℝ)*X 1 0+(4414189129/10000000000 : ℝ)*X 1 1+(882838239/2000000000 : ℝ)*X 1 2+(252471497/625000000 : ℝ)*X 2 0+(4414189129/10000000000 : ℝ)*X 2 1+(882838239/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1480_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31851/50000 : ℝ) ≤ (-248905985921796299346800298711569/390750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17075179/100000000000000 : ℝ)*(lower2) + (15676939/50000000000000 : ℝ)*(lower3) + (11361919/100000000000000 : ℝ)*(upper5) + (1087864196738731/50000000000000 : ℝ)*(major0) + (1087864196738731/50000000000000 : ℝ)*(major1) + (1087864196738731/50000000000000 : ℝ)*(major2) + (427020263/10000000000000 : ℝ)*(sp2) + (1509925158814693/50000000000000 : ℝ)*(sp4) + (377475805251333/12500000000000 : ℝ)*(sp5) + (94370366749409/3125000000000 : ℝ)*(sp6) + (1352793812412797/100000000000000 : ℝ)*(sp7) + (1422138583/25000000000000 : ℝ)*(sp12) + (49564173053/100000000000000 : ℝ)*(sp13) + (40151205219/100000000000000 : ℝ)*(sp15) + (42276061363063/3125000000000 : ℝ)*(f.failure) + (1509928003091859/50000000000000 : ℝ)*(f.sum) + (116180700258559/23445000000000000000000000000 : ℝ)*base66 + (1514477720232111569/2344500000000000000000000000000000 : ℝ)*base67 + (2960084948179388431/2344500000000000000000000000000000 : ℝ)*base70 + (15178700354737611569/2344500000000000000000000000000000 : ℝ)*base71 + (25064248518113/2930625000000000000000000000 : ℝ)*base74 + (31197615236437611569/2344500000000000000000000000000000 : ℝ)*base75 + (3062067411190388431/2344500000000000000000000000000000 : ℝ)*base78 + (7745468152446111569/2344500000000000000000000000000000 : ℝ)*base79 + (119586477946279/23445000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (113869/78125000000000000000 : ℝ)*base89 + (113869/78125000000000000000 : ℝ)*base91 + (113869/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29239/50000 : ℝ) ≤ (2285115488865766079617118087/3907500000000000000000000000 : ℝ) := by norm_num
    linear_combination (24975091/20000000000000 : ℝ)*(lower0) + (845079/5000000000000 : ℝ)*(upper1) + (149302947/100000000000000 : ℝ)*(upper2) + (281224470674111/12500000000000 : ℝ)*(major0) + (281224470674111/12500000000000 : ℝ)*(major1) + (281224470674111/12500000000000 : ℝ)*(major2) + (1540604433136719/50000000000000 : ℝ)*(sp0) + (308118910872021/10000000000000 : ℝ)*(sp1) + (77029150205659/2500000000000 : ℝ)*(sp2) + (349721415814963/25000000000000 : ℝ)*(sp3) + (2236420911/100000000000000 : ℝ)*(sp7) + (21108105707/100000000000000 : ℝ)*(sp9) + (44208599559/100000000000000 : ℝ)*(sp10) + (1350552481/100000000000000 : ℝ)*(sp12) + (349721974920191/25000000000000 : ℝ)*(f.failure) + (1540605108412959/50000000000000 : ℝ)*(f.sum) + (9761085365531/23445000000000000000000000000 : ℝ)*base66 + (632177978064829811/586125000000000000000000000000000 : ℝ)*base68 + (51410203887295189/586125000000000000000000000000000 : ℝ)*base69 + (3090915934966045189/586125000000000000000000000000000 : ℝ)*base71 + (76830029890241/23445000000000000000000000000 : ℝ)*base74 + (5649379155903295189/586125000000000000000000000000000 : ℝ)*base75 + (4404223287445579811/586125000000000000000000000000000 : ℝ)*base78 + (3820684058768329811/586125000000000000000000000000000 : ℝ)*base80 + (120576138250639/23445000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (5470833/625000000000000000000 : ℝ)*base89 + (5470833/625000000000000000000 : ℝ)*base91 + (5470833/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (2499/3125 : ℝ) ≤ (312484637708520198844829373639437/390750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19636697/50000000000000 : ℝ)*(upper0) + (13956721/50000000000000 : ℝ)*(upper2) + (13502753/100000000000000 : ℝ)*(lower3) + (11995577/25000000000000 : ℝ)*(lower5) + (1223646437079179/50000000000000 : ℝ)*(major0) + (1223646437079179/50000000000000 : ℝ)*(major1) + (1223646437079179/50000000000000 : ℝ)*(major2) + (98516465587/100000000000000 : ℝ)*(sp1) + (17564047/20000000000000 : ℝ)*(sp4) + (1673118624498977/50000000000000 : ℝ)*(sp8) + (104566933945101/3125000000000 : ℝ)*(sp9) + (167312020135441/5000000000000 : ℝ)*(sp10) + (1521688520040943/100000000000000 : ℝ)*(sp11) + (306589063/10000000000000 : ℝ)*(sp12) + (1521688520040943/100000000000000 : ℝ)*(f.failure) + (167312020135441/5000000000000 : ℝ)*(f.sum) + (206498127645281/23445000000000000000000000000 : ℝ)*base66 + (28056249563194853521/2344500000000000000000000000000000 : ℝ)*base67 + (10351359932788853521/2344500000000000000000000000000000 : ℝ)*base69 + (19910813253495353521/2344500000000000000000000000000000 : ℝ)*base71 + (180448836944569/23445000000000000000000000000 : ℝ)*base73 + (9268225064727353521/2344500000000000000000000000000000 : ℝ)*base75 + (553719005493353521/2344500000000000000000000000000000 : ℝ)*base77 + (5735702588680853521/2344500000000000000000000000000000 : ℝ)*base79 + (113125368748871/23445000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (408191/2500000000000000000000 : ℝ)*base90 + (408191/2500000000000000000000 : ℝ)*base92 + (408191/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42897/50000 : ℝ) ≤ (-2234858607264132473100587083/2605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84574841/50000000000000 : ℝ)*(lower1) + (168896881/100000000000000 : ℝ)*(lower3) + (29725779/25000000000000 : ℝ)*(lower4) + (6070641/50000000000000 : ℝ)*(upper5) + (1242806490252471/50000000000000 : ℝ)*(major0) + (1242806490252471/50000000000000 : ℝ)*(major1) + (1242806490252471/50000000000000 : ℝ)*(major2) + (6052311721/100000000000000 : ℝ)*(sp4) + (109351049573/100000000000000 : ℝ)*(sp6) + (36725606077/50000000000000 : ℝ)*(sp7) + (1727150791811311/50000000000000 : ℝ)*(sp12) + (3454307635934343/100000000000000 : ℝ)*(sp13) + (345419828488477/10000000000000 : ℝ)*(sp14) + (1545441912983843/100000000000000 : ℝ)*(sp15) + (772757682097999/50000000000000 : ℝ)*(f.failure) + (3454307635934343/100000000000000 : ℝ)*(f.sum) + (27259089016517/7815000000000000000000000000 : ℝ)*base65 + (273708250628680057/781500000000000000000000000000000 : ℝ)*base68 + (5324367236669680057/781500000000000000000000000000000 : ℝ)*base70 + (3027641034598819943/781500000000000000000000000000000 : ℝ)*base71 + (1878497153323/7815000000000000000000000000 : ℝ)*base74 + (4714754476115680057/781500000000000000000000000000000 : ℝ)*base76 + (2407679844075319943/781500000000000000000000000000000 : ℝ)*base77 + (542310461356819943/781500000000000000000000000000000 : ℝ)*base79 + (1639560858793/7815000000000000000000000000 : ℝ)*base82 + (23367137/1250000000000000000000 : ℝ)*base89 + (23367137/1250000000000000000000 : ℝ)*base91 + (23367137/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1480_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (619/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5393/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31851/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29239/50000 : ℝ) else (2499/3125 : ℝ) ≤ X j i ∧ X j i ≤ (42897/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1480_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1480_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31851/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29239/50000 : ℝ) else (2499/3125 : ℝ) ≤ X j i ∧ X j i ≤ (42897/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1480_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1480_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4455/1024 : ℝ) ≤ p) (hpb : p ≤ (4457/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40206863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2157/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31851/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29239/50000 : ℝ) else (2499/3125 : ℝ) ≤ X j i ∧ X j i ≤ (42897/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1480_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
