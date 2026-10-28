-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:22:20.942985+00:00
-- url     : https://prove2.me/submissions/701fc92b-3203-4f3f-8374-b47ad88c1124

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
theorem support_rectangle_w1248_s3_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114406251/10000000000 : ℝ)*x 0 + (5419145233/10000000000 : ℝ)*x 1 + (327566787/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114406251/10000000000 : ℝ)^8441 ≤ (6426615167069/50000000000000 : ℝ)^6393 := by
    have hnat : (2114406251 : ℕ)^8441*50000000000000^6393 ≤ 6426615167069^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114406251 10000000000 6426615167069 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419145233/10000000000 : ℝ)^8441 ≤ (44534380658743/100000000000000 : ℝ)^6393 := by
    have hnat : (5419145233 : ℕ)^8441*100000000000000^6393 ≤ 44534380658743^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419145233 10000000000 44534380658743 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327566787/625000000 : ℝ)^8441 ≤ (21306194496113/50000000000000 : ℝ)^6393 := by
    have hnat : (327566787 : ℕ)^8441*50000000000000^6393 ≤ 21306194496113^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327566787 625000000 21306194496113 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114406251/10000000000 : ℝ), (5419145233/10000000000 : ℝ), (327566787/625000000 : ℝ)] ![(6426615167069/50000000000000 : ℝ), (44534380658743/100000000000000 : ℝ), (21306194496113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114406251/10000000000 : ℝ)|^8441 ≤ (6426615167069/50000000000000 : ℝ)^6393
        have hw : |(-2114406251/10000000000 : ℝ)|=(2114406251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419145233/10000000000 : ℝ)|^8441 ≤ (44534380658743/100000000000000 : ℝ)^6393
        have hw : |(5419145233/10000000000 : ℝ)|=(5419145233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327566787/625000000 : ℝ)|^8441 ≤ (21306194496113/50000000000000 : ℝ)^6393
        have hw : |(327566787/625000000 : ℝ)|=(327566787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675680231/5000000000 : ℝ)*x 0 + (-551310089/2500000000 : ℝ)*x 1 + (52410687/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675680231/5000000000 : ℝ)^8441 ≤ (43800352914073/100000000000000 : ℝ)^6393 := by
    have hnat : (2675680231 : ℕ)^8441*100000000000000^6393 ≤ 43800352914073^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675680231 5000000000 43800352914073 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551310089/2500000000 : ℝ)^8441 ≤ (3396814230191/25000000000000 : ℝ)^6393 := by
    have hnat : (551310089 : ℕ)^8441*25000000000000^6393 ≤ 3396814230191^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551310089 2500000000 3396814230191 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52410687/100000000 : ℝ)^8441 ≤ (8522478030323/20000000000000 : ℝ)^6393 := by
    have hnat : (52410687 : ℕ)^8441*20000000000000^6393 ≤ 8522478030323^6393*100000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52410687 100000000 8522478030323 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675680231/5000000000 : ℝ), (-551310089/2500000000 : ℝ), (52410687/100000000 : ℝ)] ![(43800352914073/100000000000000 : ℝ), (3396814230191/25000000000000 : ℝ), (8522478030323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675680231/5000000000 : ℝ)|^8441 ≤ (43800352914073/100000000000000 : ℝ)^6393
        have hw : |(2675680231/5000000000 : ℝ)|=(2675680231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551310089/2500000000 : ℝ)|^8441 ≤ (3396814230191/25000000000000 : ℝ)^6393
        have hw : |(-551310089/2500000000 : ℝ)|=(551310089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52410687/100000000 : ℝ)|^8441 ≤ (8522478030323/20000000000000 : ℝ)^6393
        have hw : |(52410687/100000000 : ℝ)|=(52410687/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675680201/5000000000 : ℝ)*x 0 + (5241069153/10000000000 : ℝ)*x 1 + (-2205239837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675680201/5000000000 : ℝ)^8441 ≤ (43800352265657/100000000000000 : ℝ)^6393 := by
    have hnat : (2675680201 : ℕ)^8441*100000000000000^6393 ≤ 43800352265657^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675680201 5000000000 43800352265657 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241069153/10000000000 : ℝ)^8441 ≤ (8522479002921/20000000000000 : ℝ)^6393 := by
    have hnat : (5241069153 : ℕ)^8441*20000000000000^6393 ≤ 8522479002921^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241069153 10000000000 8522479002921 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205239837/10000000000 : ℝ)^8441 ≤ (13587252698627/100000000000000 : ℝ)^6393 := by
    have hnat : (2205239837 : ℕ)^8441*100000000000000^6393 ≤ 13587252698627^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205239837 10000000000 13587252698627 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675680201/5000000000 : ℝ), (5241069153/10000000000 : ℝ), (-2205239837/10000000000 : ℝ)] ![(43800352265657/100000000000000 : ℝ), (8522479002921/20000000000000 : ℝ), (13587252698627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675680201/5000000000 : ℝ)|^8441 ≤ (43800352265657/100000000000000 : ℝ)^6393
        have hw : |(2675680201/5000000000 : ℝ)|=(2675680201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241069153/10000000000 : ℝ)|^8441 ≤ (8522479002921/20000000000000 : ℝ)^6393
        have hw : |(5241069153/10000000000 : ℝ)|=(5241069153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205239837/10000000000 : ℝ)|^8441 ≤ (13587252698627/100000000000000 : ℝ)^6393
        have hw : |(-2205239837/10000000000 : ℝ)|=(2205239837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869656087/2000000000 : ℝ)*x 0 + (1042774601/2500000000 : ℝ)*x 1 + (113318911/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869656087/2000000000 : ℝ)^8441 ≤ (3330062867029/10000000000000 : ℝ)^6393 := by
    have hnat : (869656087 : ℕ)^8441*10000000000000^6393 ≤ 3330062867029^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869656087 2000000000 3330062867029 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042774601/2500000000 : ℝ)^8441 ≤ (15760410377967/50000000000000 : ℝ)^6393 := by
    have hnat : (1042774601 : ℕ)^8441*50000000000000^6393 ≤ 15760410377967^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042774601 2500000000 15760410377967 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113318911/250000000 : ℝ)^8441 ≤ (8794637639551/25000000000000 : ℝ)^6393 := by
    have hnat : (113318911 : ℕ)^8441*25000000000000^6393 ≤ 8794637639551^6393*250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113318911 250000000 8794637639551 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869656087/2000000000 : ℝ), (1042774601/2500000000 : ℝ), (113318911/250000000 : ℝ)] ![(3330062867029/10000000000000 : ℝ), (15760410377967/50000000000000 : ℝ), (8794637639551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869656087/2000000000 : ℝ)|^8441 ≤ (3330062867029/10000000000000 : ℝ)^6393
        have hw : |(869656087/2000000000 : ℝ)|=(869656087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042774601/2500000000 : ℝ)|^8441 ≤ (15760410377967/50000000000000 : ℝ)^6393
        have hw : |(1042774601/2500000000 : ℝ)|=(1042774601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113318911/250000000 : ℝ)|^8441 ≤ (8794637639551/25000000000000 : ℝ)^6393
        have hw : |(113318911/250000000 : ℝ)|=(113318911/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114420371/10000000000 : ℝ)*x 0 + (2620856851/5000000000 : ℝ)*x 1 + (5418496521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114420371/10000000000 : ℝ)^8441 ≤ (2570668733001/20000000000000 : ℝ)^6393 := by
    have hnat : (2114420371 : ℕ)^8441*20000000000000^6393 ≤ 2570668733001^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114420371 10000000000 2570668733001 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620856851/5000000000 : ℝ)^8441 ≤ (42619314435419/100000000000000 : ℝ)^6393 := by
    have hnat : (2620856851 : ℕ)^8441*100000000000000^6393 ≤ 42619314435419^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620856851 5000000000 42619314435419 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418496521/10000000000 : ℝ)^8441 ≤ (44527341878171/100000000000000 : ℝ)^6393 := by
    have hnat : (5418496521 : ℕ)^8441*100000000000000^6393 ≤ 44527341878171^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418496521 10000000000 44527341878171 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114420371/10000000000 : ℝ), (2620856851/5000000000 : ℝ), (5418496521/10000000000 : ℝ)] ![(2570668733001/20000000000000 : ℝ), (42619314435419/100000000000000 : ℝ), (44527341878171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114420371/10000000000 : ℝ)|^8441 ≤ (2570668733001/20000000000000 : ℝ)^6393
        have hw : |(-2114420371/10000000000 : ℝ)|=(2114420371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620856851/5000000000 : ℝ)|^8441 ≤ (42619314435419/100000000000000 : ℝ)^6393
        have hw : |(2620856851/5000000000 : ℝ)|=(2620856851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418496521/10000000000 : ℝ)|^8441 ≤ (44527341878171/100000000000000 : ℝ)^6393
        have hw : |(5418496521/10000000000 : ℝ)|=(5418496521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663238807/1250000000 : ℝ)*x 0 + (-2027812461/10000000000 : ℝ)*x 1 + (5418496743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663238807/1250000000 : ℝ)^8441 ≤ (8661969413509/20000000000000 : ℝ)^6393 := by
    have hnat : (663238807 : ℕ)^8441*20000000000000^6393 ≤ 8661969413509^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663238807 1250000000 8661969413509 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027812461/10000000000 : ℝ)^8441 ≤ (6081404315633/50000000000000 : ℝ)^6393 := by
    have hnat : (2027812461 : ℕ)^8441*50000000000000^6393 ≤ 6081404315633^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027812461 10000000000 6081404315633 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418496743/10000000000 : ℝ)^8441 ≤ (695739754483/1562500000000 : ℝ)^6393 := by
    have hnat : (5418496743 : ℕ)^8441*1562500000000^6393 ≤ 695739754483^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418496743 10000000000 695739754483 1562500000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663238807/1250000000 : ℝ), (-2027812461/10000000000 : ℝ), (5418496743/10000000000 : ℝ)] ![(8661969413509/20000000000000 : ℝ), (6081404315633/50000000000000 : ℝ), (695739754483/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663238807/1250000000 : ℝ)|^8441 ≤ (8661969413509/20000000000000 : ℝ)^6393
        have hw : |(663238807/1250000000 : ℝ)|=(663238807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027812461/10000000000 : ℝ)|^8441 ≤ (6081404315633/50000000000000 : ℝ)^6393
        have hw : |(-2027812461/10000000000 : ℝ)|=(2027812461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418496743/10000000000 : ℝ)|^8441 ≤ (695739754483/1562500000000 : ℝ)^6393
        have hw : |(5418496743/10000000000 : ℝ)|=(5418496743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106118211/200000000 : ℝ)*x 0 + (5418496653/10000000000 : ℝ)*x 1 + (-2027812457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106118211/200000000 : ℝ)^8441 ≤ (69295756929/160000000000 : ℝ)^6393 := by
    have hnat : (106118211 : ℕ)^8441*160000000000^6393 ≤ 69295756929^6393*200000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106118211 200000000 69295756929 160000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418496653/10000000000 : ℝ)^8441 ≤ (8905468662079/20000000000000 : ℝ)^6393 := by
    have hnat : (5418496653 : ℕ)^8441*20000000000000^6393 ≤ 8905468662079^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418496653 10000000000 8905468662079 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2027812457/10000000000 : ℝ)^8441 ≤ (3040702149897/25000000000000 : ℝ)^6393 := by
    have hnat : (2027812457 : ℕ)^8441*25000000000000^6393 ≤ 3040702149897^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027812457 10000000000 3040702149897 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106118211/200000000 : ℝ), (5418496653/10000000000 : ℝ), (-2027812457/10000000000 : ℝ)] ![(69295756929/160000000000 : ℝ), (8905468662079/20000000000000 : ℝ), (3040702149897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106118211/200000000 : ℝ)|^8441 ≤ (69295756929/160000000000 : ℝ)^6393
        have hw : |(106118211/200000000 : ℝ)|=(106118211/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418496653/10000000000 : ℝ)|^8441 ≤ (8905468662079/20000000000000 : ℝ)^6393
        have hw : |(5418496653/10000000000 : ℝ)|=(5418496653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2027812457/10000000000 : ℝ)|^8441 ≤ (3040702149897/25000000000000 : ℝ)^6393
        have hw : |(-2027812457/10000000000 : ℝ)|=(2027812457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s3_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543538581/1250000000 : ℝ)*x 0 + (2265723487/5000000000 : ℝ)*x 1 + (8344829/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543538581/1250000000 : ℝ)^8441 ≤ (33300913951917/100000000000000 : ℝ)^6393 := by
    have hnat : (543538581 : ℕ)^8441*100000000000000^6393 ≤ 33300913951917^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543538581 1250000000 33300913951917 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265723487/5000000000 : ℝ)^8441 ≤ (7033026566667/20000000000000 : ℝ)^6393 := by
    have hnat : (2265723487 : ℕ)^8441*20000000000000^6393 ≤ 7033026566667^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265723487 5000000000 7033026566667 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8344829/20000000 : ℝ)^8441 ≤ (31533953207071/100000000000000 : ℝ)^6393 := by
    have hnat : (8344829 : ℕ)^8441*100000000000000^6393 ≤ 31533953207071^6393*20000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8344829 20000000 31533953207071 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543538581/1250000000 : ℝ), (2265723487/5000000000 : ℝ), (8344829/20000000 : ℝ)] ![(33300913951917/100000000000000 : ℝ), (7033026566667/20000000000000 : ℝ), (31533953207071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543538581/1250000000 : ℝ)|^8441 ≤ (33300913951917/100000000000000 : ℝ)^6393
        have hw : |(543538581/1250000000 : ℝ)|=(543538581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265723487/5000000000 : ℝ)|^8441 ≤ (7033026566667/20000000000000 : ℝ)^6393
        have hw : |(2265723487/5000000000 : ℝ)|=(2265723487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8344829/20000000 : ℝ)|^8441 ≤ (31533953207071/100000000000000 : ℝ)^6393
        have hw : |(8344829/20000000 : ℝ)|=(8344829/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5463/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1837/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1013/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9523/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1013/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9523/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1013/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9523/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1013/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9523/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1013/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9523/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1013/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9523/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9523/100000 : ℝ) ^ (1055/256 : ℝ) ≤ (386643793002497/6250000000000000000 : ℝ) := by
    have hpowers : (9523/100000 : ℝ)^1055 ≤ (386643793002497/6250000000000000000 : ℝ)^256 := by
      have hnat : (9523 : ℕ)^1055*6250000000000000000^256 ≤ 386643793002497^256*100000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9523 100000 386643793002497 6250000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9523/100000 : ℝ)) (X := (386643793002497/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1013/6250 : ℝ) ^ (1055/256 : ℝ) ≤ (5536316182507741/10000000000000000000 : ℝ) := by
    have hpowers : (1013/6250 : ℝ)^1055 ≤ (5536316182507741/10000000000000000000 : ℝ)^256 := by
      have hnat : (1013 : ℕ)^1055*10000000000000000000^256 ≤ 5536316182507741^256*6250^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1013 6250 5536316182507741 10000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1013/6250 : ℝ)) (X := (5536316182507741/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125386643793002497/3125000000000000000 : ℝ) ≤ (1250037526511441/1250000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (3125386643793002497/3125000000000000000 : ℝ)^256 ≤ (1250037526511441/1250000000000000 : ℝ)^1055 := by
      have hnat : (3125386643793002497 : ℕ)^256*1250000000000000^1055 ≤ 1250037526511441^1055*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125386643793002497 3125000000000000000 1250037526511441 1250000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250037526511441/1250000000000000 : ℝ)) (X := (3125386643793002497/3125000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50030774731256558681/50000000000000000000 : ℝ) ≤ (10001493174531077/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50030774731256558681/50000000000000000000 : ℝ)^256 ≤ (10001493174531077/10000000000000000 : ℝ)^1055 := by
      have hnat : (50030774731256558681 : ℕ)^256*10000000000000000^1055 ≤ 10001493174531077^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030774731256558681 50000000000000000000 10001493174531077 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001493174531077/10000000000000000 : ℝ)) (X := (50030774731256558681/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5005536316182507741/5000000000000000000 : ℝ) ≤ (5001343068485313/5000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (5005536316182507741/5000000000000000000 : ℝ)^256 ≤ (5001343068485313/5000000000000000 : ℝ)^1055 := by
      have hnat : (5005536316182507741 : ℕ)^256*5000000000000000^1055 ≤ 5001343068485313^1055*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5005536316182507741 5000000000000000000 5001343068485313 5000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001343068485313/5000000000000000 : ℝ)) (X := (5005536316182507741/5000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(386643793002497/6250000000000000000 : ℝ) ≤ ((33414642877604107213/33425000000000000000 : ℝ)+2*(1192962439549/668500000000000 : ℝ)*(9523/100000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (33414642877604107213/33425000000000000000 : ℝ)+2*(1192962439549/668500000000000 : ℝ)*(9523/100000 : ℝ)=(1250037526511441/1250000000000000 : ℝ) by norm_num, show 1+2*(386643793002497/6250000000000000000 : ℝ)=(3125386643793002497/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5536316182507741/10000000000000000000 : ℝ)+(386643793002497/6250000000000000000 : ℝ) ≤ ((33414642877604107213/33425000000000000000 : ℝ)+(1192962439549/668500000000000 : ℝ)*((1013/6250 : ℝ)+(9523/100000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (33414642877604107213/33425000000000000000 : ℝ)+(1192962439549/668500000000000 : ℝ)*((1013/6250 : ℝ)+(9523/100000 : ℝ))=(10001493174531077/10000000000000000 : ℝ) by norm_num, show 1+(5536316182507741/10000000000000000000 : ℝ)+(386643793002497/6250000000000000000 : ℝ)=(50030774731256558681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5536316182507741/10000000000000000000 : ℝ) ≤ ((33414642877604107213/33425000000000000000 : ℝ)+2*(1192962439549/668500000000000 : ℝ)*(1013/6250 : ℝ))^(1055/256 : ℝ) := by
    rw [show (33414642877604107213/33425000000000000000 : ℝ)+2*(1192962439549/668500000000000 : ℝ)*(1013/6250 : ℝ)=(5001343068485313/5000000000000000 : ℝ) by norm_num, show 1+2*(5536316182507741/10000000000000000000 : ℝ)=(5005536316182507741/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33414642877604107213/33425000000000000000 : ℝ)*(X 1 0+X 2 0)+(1192962439549/668500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (9523/100000 : ℝ)) (hi := (1013/6250 : ℝ)) (c := (33414642877604107213/33425000000000000000 : ℝ)) (alpha := (1192962439549/668500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33414642877604107213/33425000000000000000 : ℝ)*(X 0 1+X 2 1)+(1192962439549/668500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (9523/100000 : ℝ)) (hi := (1013/6250 : ℝ)) (c := (33414642877604107213/33425000000000000000 : ℝ)) (alpha := (1192962439549/668500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33414642877604107213/33425000000000000000 : ℝ)*(X 0 2+X 1 2)+(1192962439549/668500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (9523/100000 : ℝ)) (hi := (1013/6250 : ℝ)) (c := (33414642877604107213/33425000000000000000 : ℝ)) (alpha := (1192962439549/668500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114406251/10000000000 : ℝ)*X 0 0+(5419145233/10000000000 : ℝ)*X 0 1+(327566787/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675680231/5000000000 : ℝ)*X 1 0+(-551310089/2500000000 : ℝ)*X 1 1+(52410687/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675680201/5000000000 : ℝ)*X 2 0+(5241069153/10000000000 : ℝ)*X 2 1+(-2205239837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869656087/2000000000 : ℝ)*X 0 0+(1042774601/2500000000 : ℝ)*X 0 1+(113318911/250000000 : ℝ)*X 0 2+(869656087/2000000000 : ℝ)*X 1 0+(1042774601/2500000000 : ℝ)*X 1 1+(113318911/250000000 : ℝ)*X 1 2+(869656087/2000000000 : ℝ)*X 2 0+(1042774601/2500000000 : ℝ)*X 2 1+(113318911/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2114420371/10000000000 : ℝ)*X 0 0+(2620856851/5000000000 : ℝ)*X 0 1+(5418496521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663238807/1250000000 : ℝ)*X 1 0+(-2027812461/10000000000 : ℝ)*X 1 1+(5418496743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106118211/200000000 : ℝ)*X 2 0+(5418496653/10000000000 : ℝ)*X 2 1+(-2027812457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543538581/1250000000 : ℝ)*X 0 0+(2265723487/5000000000 : ℝ)*X 0 1+(8344829/20000000 : ℝ)*X 0 2+(543538581/1250000000 : ℝ)*X 1 0+(2265723487/5000000000 : ℝ)*X 1 1+(8344829/20000000 : ℝ)*X 1 2+(543538581/1250000000 : ℝ)*X 2 0+(2265723487/5000000000 : ℝ)*X 2 1+(8344829/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (972080445460754761388644329/104453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1346789157/100000000000000 : ℝ)*(base19) + (895263359/100000000000000 : ℝ)*(base23) + (226113943/100000000000000 : ℝ)*(lower2) + (66223369/50000000000000 : ℝ)*(upper5) + (261897093260263/6250000000000 : ℝ)*(major0) + (261897093260263/6250000000000 : ℝ)*(major1) + (261897093260263/6250000000000 : ℝ)*(major2) + (561559367189801/10000000000000 : ℝ)*(sp0) + (5615631866608231/100000000000000 : ℝ)*(sp1) + (5615636318140217/100000000000000 : ℝ)*(sp2) + (1382528156676477/50000000000000 : ℝ)*(sp3) + (43541505567/100000000000000 : ℝ)*(sp4) + (1000001547/25000000000000 : ℝ)*(sp5) + (13147359217/100000000000000 : ℝ)*(sp7) + (691267365178043/25000000000000 : ℝ)*(f.failure) + (701954651675447/12500000000000 : ℝ)*(f.sum) + (11286035463883/33425000000000000000000000000 : ℝ)*base66 + (2557591499367364519/208906250000000000000000000000000 : ℝ)*base67 + (1152489221505958269/208906250000000000000000000000000 : ℝ)*base69 + (2191416881185177019/208906250000000000000000000000000 : ℝ)*base71 + (30804134878721/16712500000000000000000000000 : ℝ)*base73 + (1322877116317052019/208906250000000000000000000000000 : ℝ)*base75 + (2369734496465177019/208906250000000000000000000000000 : ℝ)*base77 + (4136805587012833269/208906250000000000000000000000000 : ℝ)*base79 + (49980416253983/33425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (516001/39062500000000000000 : ℝ)*base89 + (516001/39062500000000000000 : ℝ)*base91 + (516001/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10006137859077175796524813761/835625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170623447/10000000000000 : ℝ)*(base19) + (2101035219/100000000000000 : ℝ)*(base23) + (152589109/50000000000000 : ℝ)*(upper3) + (14623753/12500000000000 : ℝ)*(lower4) + (5590653/3125000000000 : ℝ)*(upper5) + (2110479448310467/50000000000000 : ℝ)*(major0) + (2110479448310467/50000000000000 : ℝ)*(major1) + (2110479448310467/50000000000000 : ℝ)*(major2) + (8483880789/25000000000000 : ℝ)*(sp1) + (1064646913/2500000000000 : ℝ)*(sp2) + (226266099385267/4000000000000 : ℝ)*(sp4) + (5656616842874049/100000000000000 : ℝ)*(sp5) + (44192248419687/781250000000 : ℝ)*(sp6) + (1392632454731163/50000000000000 : ℝ)*(sp7) + (1392632454731163/50000000000000 : ℝ)*(f.failure) + (226266099385267/4000000000000 : ℝ)*(f.sum) + (258392835634991/33425000000000000000000000000 : ℝ)*base65 + (1730279065699748471/1671250000000000000000000000000000 : ℝ)*base67 + (1525689151403498471/1671250000000000000000000000000000 : ℝ)*base69 + (20942973594787248471/1671250000000000000000000000000000 : ℝ)*base71 + (35618463942809/33425000000000000000000000000 : ℝ)*base74 + (15984279678798498471/1671250000000000000000000000000000 : ℝ)*base75 + (7617643727427248471/1671250000000000000000000000000000 : ℝ)*base77 + (16076872468992248471/1671250000000000000000000000000000 : ℝ)*base79 + (8916334963183/16712500000000000000000000000 : ℝ)*base81 + (701659/78125000000000000000 : ℝ)*base90 + (701659/78125000000000000000 : ℝ)*base92 + (701659/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1248_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5463/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1248_s4_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21166611/100000000 : ℝ)*x 0 + (5397260347/10000000000 : ℝ)*x 1 + (2630737893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21166611/100000000 : ℝ)^8441 ≤ (6435665710979/50000000000000 : ℝ)^6393 := by
    have hnat : (21166611 : ℕ)^8441*50000000000000^6393 ≤ 6435665710979^6393*100000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21166611 100000000 6435665710979 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397260347/10000000000 : ℝ)^8441 ≤ (44297070223443/100000000000000 : ℝ)^6393 := by
    have hnat : (5397260347 : ℕ)^8441*100000000000000^6393 ≤ 44297070223443^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397260347 10000000000 44297070223443 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630737893/5000000000 : ℝ)^8441 ≤ (42831598337181/100000000000000 : ℝ)^6393 := by
    have hnat : (2630737893 : ℕ)^8441*100000000000000^6393 ≤ 42831598337181^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630737893 5000000000 42831598337181 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21166611/100000000 : ℝ), (5397260347/10000000000 : ℝ), (2630737893/5000000000 : ℝ)] ![(6435665710979/50000000000000 : ℝ), (44297070223443/100000000000000 : ℝ), (42831598337181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21166611/100000000 : ℝ)|^8441 ≤ (6435665710979/50000000000000 : ℝ)^6393
        have hw : |(-21166611/100000000 : ℝ)|=(21166611/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397260347/10000000000 : ℝ)|^8441 ≤ (44297070223443/100000000000000 : ℝ)^6393
        have hw : |(5397260347/10000000000 : ℝ)|=(5397260347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630737893/5000000000 : ℝ)|^8441 ≤ (42831598337181/100000000000000 : ℝ)^6393
        have hw : |(2630737893/5000000000 : ℝ)|=(2630737893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336460159/2500000000 : ℝ)*x 0 + (-2185597903/10000000000 : ℝ)*x 1 + (5261475789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336460159/2500000000 : ℝ)^8441 ≤ (43740710362879/100000000000000 : ℝ)^6393 := by
    have hnat : (1336460159 : ℕ)^8441*100000000000000^6393 ≤ 43740710362879^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336460159 2500000000 43740710362879 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185597903/10000000000 : ℝ)^8441 ≤ (2685538249871/20000000000000 : ℝ)^6393 := by
    have hnat : (2185597903 : ℕ)^8441*20000000000000^6393 ≤ 2685538249871^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185597903 10000000000 2685538249871 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261475789/10000000000 : ℝ)^8441 ≤ (42831598369427/100000000000000 : ℝ)^6393 := by
    have hnat : (5261475789 : ℕ)^8441*100000000000000^6393 ≤ 42831598369427^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261475789 10000000000 42831598369427 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336460159/2500000000 : ℝ), (-2185597903/10000000000 : ℝ), (5261475789/10000000000 : ℝ)] ![(43740710362879/100000000000000 : ℝ), (2685538249871/20000000000000 : ℝ), (42831598369427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336460159/2500000000 : ℝ)|^8441 ≤ (43740710362879/100000000000000 : ℝ)^6393
        have hw : |(1336460159/2500000000 : ℝ)|=(1336460159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185597903/10000000000 : ℝ)|^8441 ≤ (2685538249871/20000000000000 : ℝ)^6393
        have hw : |(-2185597903/10000000000 : ℝ)|=(2185597903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261475789/10000000000 : ℝ)|^8441 ≤ (42831598369427/100000000000000 : ℝ)^6393
        have hw : |(5261475789/10000000000 : ℝ)|=(5261475789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345840729/10000000000 : ℝ)*x 0 + (328842229/625000000 : ℝ)*x 1 + (-273199743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345840729/10000000000 : ℝ)^8441 ≤ (5467588920949/12500000000000 : ℝ)^6393 := by
    have hnat : (5345840729 : ℕ)^8441*12500000000000^6393 ≤ 5467588920949^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345840729 10000000000 5467588920949 12500000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328842229/625000000 : ℝ)^8441 ≤ (4283159702587/10000000000000 : ℝ)^6393 := by
    have hnat : (328842229 : ℕ)^8441*10000000000000^6393 ≤ 4283159702587^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328842229 625000000 4283159702587 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273199743/1250000000 : ℝ)^8441 ≤ (13427691581941/100000000000000 : ℝ)^6393 := by
    have hnat : (273199743 : ℕ)^8441*100000000000000^6393 ≤ 13427691581941^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273199743 1250000000 13427691581941 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345840729/10000000000 : ℝ), (328842229/625000000 : ℝ), (-273199743/1250000000 : ℝ)] ![(5467588920949/12500000000000 : ℝ), (4283159702587/10000000000000 : ℝ), (13427691581941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345840729/10000000000 : ℝ)|^8441 ≤ (5467588920949/12500000000000 : ℝ)^6393
        have hw : |(5345840729/10000000000 : ℝ)|=(5345840729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328842229/625000000 : ℝ)|^8441 ≤ (4283159702587/10000000000000 : ℝ)^6393
        have hw : |(328842229/625000000 : ℝ)|=(328842229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273199743/1250000000 : ℝ)|^8441 ≤ (13427691581941/100000000000000 : ℝ)^6393
        have hw : |(-273199743/1250000000 : ℝ)|=(273199743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349633487/10000000000 : ℝ)*x 0 + (4213870981/10000000000 : ℝ)*x 1 + (561204857/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349633487/10000000000 : ℝ)^8441 ≤ (16657155502563/50000000000000 : ℝ)^6393 := by
    have hnat : (4349633487 : ℕ)^8441*50000000000000^6393 ≤ 16657155502563^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349633487 10000000000 16657155502563 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4213870981/10000000000 : ℝ)^8441 ≤ (1597414890031/5000000000000 : ℝ)^6393 := by
    have hnat : (4213870981 : ℕ)^8441*5000000000000^6393 ≤ 1597414890031^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213870981 10000000000 1597414890031 5000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561204857/1250000000 : ℝ)^8441 ≤ (34737391178571/100000000000000 : ℝ)^6393 := by
    have hnat : (561204857 : ℕ)^8441*100000000000000^6393 ≤ 34737391178571^6393*1250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561204857 1250000000 34737391178571 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349633487/10000000000 : ℝ), (4213870981/10000000000 : ℝ), (561204857/1250000000 : ℝ)] ![(16657155502563/50000000000000 : ℝ), (1597414890031/5000000000000 : ℝ), (34737391178571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349633487/10000000000 : ℝ)|^8441 ≤ (16657155502563/50000000000000 : ℝ)^6393
        have hw : |(4349633487/10000000000 : ℝ)|=(4349633487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4213870981/10000000000 : ℝ)|^8441 ≤ (1597414890031/5000000000000 : ℝ)^6393
        have hw : |(4213870981/10000000000 : ℝ)|=(4213870981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561204857/1250000000 : ℝ)|^8441 ≤ (34737391178571/100000000000000 : ℝ)^6393
        have hw : |(561204857/1250000000 : ℝ)|=(561204857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116667253/10000000000 : ℝ)*x 0 + (5261851311/10000000000 : ℝ)*x 1 + (5396883307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116667253/10000000000 : ℝ)^8441 ≤ (2574276164881/20000000000000 : ℝ)^6393 := by
    have hnat : (2116667253 : ℕ)^8441*20000000000000^6393 ≤ 2574276164881^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116667253 10000000000 2574276164881 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261851311/10000000000 : ℝ)^8441 ≤ (10708908673893/25000000000000 : ℝ)^6393 := by
    have hnat : (5261851311 : ℕ)^8441*25000000000000^6393 ≤ 10708908673893^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261851311 10000000000 10708908673893 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396883307/10000000000 : ℝ)^8441 ≤ (44292984458303/100000000000000 : ℝ)^6393 := by
    have hnat : (5396883307 : ℕ)^8441*100000000000000^6393 ≤ 44292984458303^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396883307 10000000000 44292984458303 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116667253/10000000000 : ℝ), (5261851311/10000000000 : ℝ), (5396883307/10000000000 : ℝ)] ![(2574276164881/20000000000000 : ℝ), (10708908673893/25000000000000 : ℝ), (44292984458303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116667253/10000000000 : ℝ)|^8441 ≤ (2574276164881/20000000000000 : ℝ)^6393
        have hw : |(-2116667253/10000000000 : ℝ)|=(2116667253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261851311/10000000000 : ℝ)|^8441 ≤ (10708908673893/25000000000000 : ℝ)^6393
        have hw : |(5261851311/10000000000 : ℝ)|=(5261851311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396883307/10000000000 : ℝ)|^8441 ≤ (44292984458303/100000000000000 : ℝ)^6393
        have hw : |(5396883307/10000000000 : ℝ)|=(5396883307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311182419/10000000000 : ℝ)*x 0 + (-128136899/625000000 : ℝ)*x 1 + (5396883219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311182419/10000000000 : ℝ)^8441 ≤ (43366674414403/100000000000000 : ℝ)^6393 := by
    have hnat : (5311182419 : ℕ)^8441*100000000000000^6393 ≤ 43366674414403^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311182419 10000000000 43366674414403 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128136899/625000000 : ℝ)^8441 ≤ (12340342058511/100000000000000 : ℝ)^6393 := by
    have hnat : (128136899 : ℕ)^8441*100000000000000^6393 ≤ 12340342058511^6393*625000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128136899 625000000 12340342058511 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396883219/10000000000 : ℝ)^8441 ≤ (44292983504709/100000000000000 : ℝ)^6393 := by
    have hnat : (5396883219 : ℕ)^8441*100000000000000^6393 ≤ 44292983504709^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396883219 10000000000 44292983504709 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311182419/10000000000 : ℝ), (-128136899/625000000 : ℝ), (5396883219/10000000000 : ℝ)] ![(43366674414403/100000000000000 : ℝ), (12340342058511/100000000000000 : ℝ), (44292983504709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311182419/10000000000 : ℝ)|^8441 ≤ (43366674414403/100000000000000 : ℝ)^6393
        have hw : |(5311182419/10000000000 : ℝ)|=(5311182419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128136899/625000000 : ℝ)|^8441 ≤ (12340342058511/100000000000000 : ℝ)^6393
        have hw : |(-128136899/625000000 : ℝ)|=(128136899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396883219/10000000000 : ℝ)|^8441 ≤ (44292983504709/100000000000000 : ℝ)^6393
        have hw : |(5396883219/10000000000 : ℝ)|=(5396883219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311182023/10000000000 : ℝ)*x 0 + (2698441871/5000000000 : ℝ)*x 1 + (-2050190209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311182023/10000000000 : ℝ)^8441 ≤ (1734666805807/4000000000000 : ℝ)^6393 := by
    have hnat : (5311182023 : ℕ)^8441*4000000000000^6393 ≤ 1734666805807^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311182023 10000000000 1734666805807 4000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698441871/5000000000 : ℝ)^8441 ≤ (8858597834419/20000000000000 : ℝ)^6393 := by
    have hnat : (2698441871 : ℕ)^8441*20000000000000^6393 ≤ 8858597834419^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698441871 5000000000 8858597834419 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050190209/10000000000 : ℝ)^8441 ≤ (493613626709/4000000000000 : ℝ)^6393 := by
    have hnat : (2050190209 : ℕ)^8441*4000000000000^6393 ≤ 493613626709^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050190209 10000000000 493613626709 4000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311182023/10000000000 : ℝ), (2698441871/5000000000 : ℝ), (-2050190209/10000000000 : ℝ)] ![(1734666805807/4000000000000 : ℝ), (8858597834419/20000000000000 : ℝ), (493613626709/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311182023/10000000000 : ℝ)|^8441 ≤ (1734666805807/4000000000000 : ℝ)^6393
        have hw : |(5311182023/10000000000 : ℝ)|=(5311182023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698441871/5000000000 : ℝ)|^8441 ≤ (8858597834419/20000000000000 : ℝ)^6393
        have hw : |(2698441871/5000000000 : ℝ)|=(2698441871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2050190209/10000000000 : ℝ)|^8441 ≤ (493613626709/4000000000000 : ℝ)^6393
        have hw : |(-2050190209/10000000000 : ℝ)|=(2050190209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s4_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349646089/10000000000 : ℝ)*x 0 + (140277389/312500000 : ℝ)*x 1 + (131707383/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349646089/10000000000 : ℝ)^8441 ≤ (16657219222751/50000000000000 : ℝ)^6393 := by
    have hnat : (4349646089 : ℕ)^8441*50000000000000^6393 ≤ 16657219222751^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349646089 10000000000 16657219222751 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140277389/312500000 : ℝ)^8441 ≤ (542650042751/1562500000000 : ℝ)^6393 := by
    have hnat : (140277389 : ℕ)^8441*1562500000000^6393 ≤ 542650042751^6393*312500000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140277389 312500000 542650042751 1562500000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131707383/312500000 : ℝ)^8441 ≤ (31955958807353/100000000000000 : ℝ)^6393 := by
    have hnat : (131707383 : ℕ)^8441*100000000000000^6393 ≤ 31955958807353^6393*312500000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131707383 312500000 31955958807353 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349646089/10000000000 : ℝ), (140277389/312500000 : ℝ), (131707383/312500000 : ℝ)] ![(16657219222751/50000000000000 : ℝ), (542650042751/1562500000000 : ℝ), (31955958807353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349646089/10000000000 : ℝ)|^8441 ≤ (16657219222751/50000000000000 : ℝ)^6393
        have hw : |(4349646089/10000000000 : ℝ)|=(4349646089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140277389/312500000 : ℝ)|^8441 ≤ (542650042751/1562500000000 : ℝ)^6393
        have hw : |(140277389/312500000 : ℝ)|=(140277389/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131707383/312500000 : ℝ)|^8441 ≤ (31955958807353/100000000000000 : ℝ)^6393
        have hw : |(131707383/312500000 : ℝ)|=(131707383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5463/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11361/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5463/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5463/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5463/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5463/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5463/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5463/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5463/50000 : ℝ) ^ (1055/256 : ℝ) ≤ (272488672956303/2500000000000000000 : ℝ) := by
    have hpowers : (5463/50000 : ℝ)^1055 ≤ (272488672956303/2500000000000000000 : ℝ)^256 := by
      have hnat : (5463 : ℕ)^1055*2500000000000000000^256 ≤ 272488672956303^256*50000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5463 50000 272488672956303 2500000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5463/50000 : ℝ)) (X := (272488672956303/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1837/12500 : ℝ) ^ (1055/256 : ℝ) ≤ (36978525887765081/100000000000000000000 : ℝ) := by
    have hpowers : (1837/12500 : ℝ)^1055 ≤ (36978525887765081/100000000000000000000 : ℝ)^256 := by
      have hnat : (1837 : ℕ)^1055*100000000000000000000^256 ≤ 36978525887765081^256*12500^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 12500 36978525887765081 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/12500 : ℝ)) (X := (36978525887765081/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250272488672956303/1250000000000000000 : ℝ) ≤ (5000264460067311/5000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (1250272488672956303/1250000000000000000 : ℝ)^256 ≤ (5000264460067311/5000000000000000 : ℝ)^1055 := by
      have hnat : (1250272488672956303 : ℕ)^256*5000000000000000^1055 ≤ 5000264460067311^1055*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250272488672956303 1250000000000000000 5000264460067311 5000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000264460067311/5000000000000000 : ℝ)) (X := (1250272488672956303/1250000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047878072806017201/100000000000000000000 : ℝ) ≤ (10001161570150681/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (100047878072806017201/100000000000000000000 : ℝ)^256 ≤ (10001161570150681/10000000000000000 : ℝ)^1055 := by
      have hnat : (100047878072806017201 : ℕ)^256*10000000000000000^1055 ≤ 10001161570150681^1055*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047878072806017201 100000000000000000000 10001161570150681 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001161570150681/10000000000000000 : ℝ)) (X := (100047878072806017201/100000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036978525887765081/50000000000000000000 : ℝ) ≤ (500089711008337/500000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50036978525887765081/50000000000000000000 : ℝ)^256 ≤ (500089711008337/500000000000000 : ℝ)^1055 := by
      have hnat : (50036978525887765081 : ℕ)^256*500000000000000^1055 ≤ 500089711008337^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036978525887765081 50000000000000000000 500089711008337 500000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500089711008337/500000000000000 : ℝ)) (X := (50036978525887765081/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(272488672956303/2500000000000000000 : ℝ) ≤ ((4711021170094575459/4712500000000000000 : ℝ)+2*(632650016059/377000000000000 : ℝ)*(5463/50000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (4711021170094575459/4712500000000000000 : ℝ)+2*(632650016059/377000000000000 : ℝ)*(5463/50000 : ℝ)=(5000264460067311/5000000000000000 : ℝ) by norm_num, show 1+2*(272488672956303/2500000000000000000 : ℝ)=(1250272488672956303/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36978525887765081/100000000000000000000 : ℝ)+(272488672956303/2500000000000000000 : ℝ) ≤ ((4711021170094575459/4712500000000000000 : ℝ)+(632650016059/377000000000000 : ℝ)*((1837/12500 : ℝ)+(5463/50000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (4711021170094575459/4712500000000000000 : ℝ)+(632650016059/377000000000000 : ℝ)*((1837/12500 : ℝ)+(5463/50000 : ℝ))=(10001161570150681/10000000000000000 : ℝ) by norm_num, show 1+(36978525887765081/100000000000000000000 : ℝ)+(272488672956303/2500000000000000000 : ℝ)=(100047878072806017201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36978525887765081/100000000000000000000 : ℝ) ≤ ((4711021170094575459/4712500000000000000 : ℝ)+2*(632650016059/377000000000000 : ℝ)*(1837/12500 : ℝ))^(1055/256 : ℝ) := by
    rw [show (4711021170094575459/4712500000000000000 : ℝ)+2*(632650016059/377000000000000 : ℝ)*(1837/12500 : ℝ)=(500089711008337/500000000000000 : ℝ) by norm_num, show 1+2*(36978525887765081/100000000000000000000 : ℝ)=(50036978525887765081/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4711021170094575459/4712500000000000000 : ℝ)*(X 1 0+X 2 0)+(632650016059/377000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5463/50000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4711021170094575459/4712500000000000000 : ℝ)) (alpha := (632650016059/377000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4711021170094575459/4712500000000000000 : ℝ)*(X 0 1+X 2 1)+(632650016059/377000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5463/50000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4711021170094575459/4712500000000000000 : ℝ)) (alpha := (632650016059/377000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4711021170094575459/4712500000000000000 : ℝ)*(X 0 2+X 1 2)+(632650016059/377000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (5463/50000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4711021170094575459/4712500000000000000 : ℝ)) (alpha := (632650016059/377000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21166611/100000000 : ℝ)*X 0 0+(5397260347/10000000000 : ℝ)*X 0 1+(2630737893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336460159/2500000000 : ℝ)*X 1 0+(-2185597903/10000000000 : ℝ)*X 1 1+(5261475789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345840729/10000000000 : ℝ)*X 2 0+(328842229/625000000 : ℝ)*X 2 1+(-273199743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349633487/10000000000 : ℝ)*X 0 0+(4213870981/10000000000 : ℝ)*X 0 1+(561204857/1250000000 : ℝ)*X 0 2+(4349633487/10000000000 : ℝ)*X 1 0+(4213870981/10000000000 : ℝ)*X 1 1+(561204857/1250000000 : ℝ)*X 1 2+(4349633487/10000000000 : ℝ)*X 2 0+(4213870981/10000000000 : ℝ)*X 2 1+(561204857/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116667253/10000000000 : ℝ)*X 0 0+(5261851311/10000000000 : ℝ)*X 0 1+(5396883307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311182419/10000000000 : ℝ)*X 1 0+(-128136899/625000000 : ℝ)*X 1 1+(5396883219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311182023/10000000000 : ℝ)*X 2 0+(2698441871/5000000000 : ℝ)*X 2 1+(-2050190209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349646089/10000000000 : ℝ)*X 0 0+(140277389/312500000 : ℝ)*X 0 1+(131707383/312500000 : ℝ)*X 0 2+(4349646089/10000000000 : ℝ)*X 1 0+(140277389/312500000 : ℝ)*X 1 1+(131707383/312500000 : ℝ)*X 1 2+(4349646089/10000000000 : ℝ)*X 2 0+(140277389/312500000 : ℝ)*X 2 1+(131707383/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1179399353377927638247137417/117812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2055727633/100000000000000 : ℝ)*(base19) + (26417689/1250000000000 : ℝ)*(base23) + (299427813/100000000000000 : ℝ)*(upper3) + (37652963/100000000000000 : ℝ)*(upper4) + (104711833/50000000000000 : ℝ)*(upper5) + (2747749986053507/50000000000000 : ℝ)*(major0) + (2747749986053507/50000000000000 : ℝ)*(major1) + (2747749986053507/50000000000000 : ℝ)*(major2) + (1841164775289763/25000000000000 : ℝ)*(sp0) + (57536773709067/781250000000 : ℝ)*(sp1) + (7364706977073089/100000000000000 : ℝ)*(sp2) + (906565741467207/25000000000000 : ℝ)*(sp3) + (49989329157/100000000000000 : ℝ)*(sp4) + (13777081543/50000000000000 : ℝ)*(sp7) + (1813145260015957/50000000000000 : ℝ)*(f.failure) + (7364709090488209/100000000000000 : ℝ)*(f.sum) + (1695196517011/1178125000000000000000000000 : ℝ)*base65 + (3361535439777377787/235625000000000000000000000000000 : ℝ)*base68 + (2756558635949877787/235625000000000000000000000000000 : ℝ)*base70 + (527889293366752787/235625000000000000000000000000000 : ℝ)*base72 + (40136625423013/9425000000000000000000000000 : ℝ)*base73 + (7436376834175502787/235625000000000000000000000000000 : ℝ)*base76 + (2100562593657377787/235625000000000000000000000000000 : ℝ)*base78 + (10395441267793002787/235625000000000000000000000000000 : ℝ)*base80 + (5463076805513/9425000000000000000000000000 : ℝ)*base81 + (4499/78125000000000000000 : ℝ)*base89 + (4499/78125000000000000000 : ℝ)*base91 + (4499/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498588127792375006783056993/235625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2836913/400000000000 : ℝ)*(base19) + (34780001/25000000000000 : ℝ)*(base23) + (52259287/20000000000000 : ℝ)*(upper3) + (55403/100000000000 : ℝ)*(upper4) + (2394307/20000000000000 : ℝ)*(upper5) + (5526040501234809/100000000000000 : ℝ)*(major0) + (5526040501234809/100000000000000 : ℝ)*(major1) + (5526040501234809/100000000000000 : ℝ)*(major2) + (6617580963/50000000000000 : ℝ)*(sp2) + (807255929/100000000000000 : ℝ)*(sp3) + (7405637772141031/100000000000000 : ℝ)*(sp4) + (7405637062912781/100000000000000 : ℝ)*(sp5) + (7405624397859101/100000000000000 : ℝ)*(sp6) + (1823221176269259/50000000000000 : ℝ)*(sp7) + (3646443159794447/100000000000000 : ℝ)*(f.failure) + (7405637772141031/100000000000000 : ℝ)*(f.sum) + (110455652742031/18850000000000000000000000000 : ℝ)*base65 + (11678296718347910169/471250000000000000000000000000000 : ℝ)*base68 + (1361311558616660169/471250000000000000000000000000000 : ℝ)*base70 + (8139815109185410169/471250000000000000000000000000000 : ℝ)*base72 + (151493934496919/18850000000000000000000000000 : ℝ)*base74 + (5619855440390839831/471250000000000000000000000000000 : ℝ)*base75 + (2952736880782089831/471250000000000000000000000000000 : ℝ)*base77 + (7577367609854160169/471250000000000000000000000000000 : ℝ)*base80 + (160734978666419/18850000000000000000000000000 : ℝ)*base82 + (549929/156250000000000000000 : ℝ)*base89 + (549929/156250000000000000000 : ℝ)*base91 + (549929/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1248_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5463/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1248_s5_0 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-52927617/250000000 : ℝ)*x 0 + (5392265573/10000000000 : ℝ)*x 1 + (1053235743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52927617/250000000 : ℝ)^8441 ≤ (12874893044359/100000000000000 : ℝ)^6393 := by
    have hnat : (52927617 : ℕ)^8441*100000000000000^6393 ≤ 12874893044359^6393*250000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52927617 250000000 12874893044359 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392265573/10000000000 : ℝ)^8441 ≤ (44242952155959/100000000000000 : ℝ)^6393 := by
    have hnat : (5392265573 : ℕ)^8441*100000000000000^6393 ≤ 44242952155959^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392265573 10000000000 44242952155959 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053235743/2000000000 : ℝ)^8441 ≤ (10720538694289/25000000000000 : ℝ)^6393 := by
    have hnat : (1053235743 : ℕ)^8441*25000000000000^6393 ≤ 10720538694289^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053235743 2000000000 10720538694289 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52927617/250000000 : ℝ), (5392265573/10000000000 : ℝ), (1053235743/2000000000 : ℝ)] ![(12874893044359/100000000000000 : ℝ), (44242952155959/100000000000000 : ℝ), (10720538694289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52927617/250000000 : ℝ)|^8441 ≤ (12874893044359/100000000000000 : ℝ)^6393
        have hw : |(-52927617/250000000 : ℝ)|=(52927617/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392265573/10000000000 : ℝ)|^8441 ≤ (44242952155959/100000000000000 : ℝ)^6393
        have hw : |(5392265573/10000000000 : ℝ)|=(5392265573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053235743/2000000000 : ℝ)|^8441 ≤ (10720538694289/25000000000000 : ℝ)^6393
        have hw : |(1053235743/2000000000 : ℝ)|=(1053235743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_1 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672287713/5000000000 : ℝ)*x 0 + (-2181048907/10000000000 : ℝ)*x 1 + (210647149/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672287713/5000000000 : ℝ)^8441 ≤ (8745408471313/20000000000000 : ℝ)^6393 := by
    have hnat : (2672287713 : ℕ)^8441*20000000000000^6393 ≤ 8745408471313^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672287713 5000000000 8745408471313 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181048907/10000000000 : ℝ)^8441 ≤ (6695401376443/50000000000000 : ℝ)^6393 := by
    have hnat : (2181048907 : ℕ)^8441*50000000000000^6393 ≤ 6695401376443^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181048907 10000000000 6695401376443 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210647149/400000000 : ℝ)^8441 ≤ (42882154884671/100000000000000 : ℝ)^6393 := by
    have hnat : (210647149 : ℕ)^8441*100000000000000^6393 ≤ 42882154884671^6393*400000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210647149 400000000 42882154884671 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672287713/5000000000 : ℝ), (-2181048907/10000000000 : ℝ), (210647149/400000000 : ℝ)] ![(8745408471313/20000000000000 : ℝ), (6695401376443/50000000000000 : ℝ), (42882154884671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672287713/5000000000 : ℝ)|^8441 ≤ (8745408471313/20000000000000 : ℝ)^6393
        have hw : |(2672287713/5000000000 : ℝ)|=(2672287713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181048907/10000000000 : ℝ)|^8441 ≤ (6695401376443/50000000000000 : ℝ)^6393
        have hw : |(-2181048907/10000000000 : ℝ)|=(2181048907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210647149/400000000 : ℝ)|^8441 ≤ (42882154884671/100000000000000 : ℝ)^6393
        have hw : |(210647149/400000000 : ℝ)|=(210647149/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_2 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672287727/5000000000 : ℝ)*x 0 + (5266178731/10000000000 : ℝ)*x 1 + (-2181048861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672287727/5000000000 : ℝ)^8441 ≤ (10931760664759/25000000000000 : ℝ)^6393 := by
    have hnat : (2672287727 : ℕ)^8441*25000000000000^6393 ≤ 10931760664759^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672287727 5000000000 10931760664759 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266178731/10000000000 : ℝ)^8441 ≤ (2144107747459/5000000000000 : ℝ)^6393 := by
    have hnat : (5266178731 : ℕ)^8441*5000000000000^6393 ≤ 2144107747459^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266178731 10000000000 2144107747459 5000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181048861/10000000000 : ℝ)^8441 ≤ (1339080237999/10000000000000 : ℝ)^6393 := by
    have hnat : (2181048861 : ℕ)^8441*10000000000000^6393 ≤ 1339080237999^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181048861 10000000000 1339080237999 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672287727/5000000000 : ℝ), (5266178731/10000000000 : ℝ), (-2181048861/10000000000 : ℝ)] ![(10931760664759/25000000000000 : ℝ), (2144107747459/5000000000000 : ℝ), (1339080237999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672287727/5000000000 : ℝ)|^8441 ≤ (10931760664759/25000000000000 : ℝ)^6393
        have hw : |(2672287727/5000000000 : ℝ)|=(2672287727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266178731/10000000000 : ℝ)|^8441 ≤ (2144107747459/5000000000000 : ℝ)^6393
        have hw : |(5266178731/10000000000 : ℝ)|=(5266178731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181048861/10000000000 : ℝ)|^8441 ≤ (1339080237999/10000000000000 : ℝ)^6393
        have hw : |(-2181048861/10000000000 : ℝ)|=(2181048861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_3 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174946189/5000000000 : ℝ)*x 0 + (2111842887/5000000000 : ℝ)*x 1 + (4479758013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174946189/5000000000 : ℝ)^8441 ≤ (16658464559287/50000000000000 : ℝ)^6393 := by
    have hnat : (2174946189 : ℕ)^8441*50000000000000^6393 ≤ 16658464559287^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174946189 5000000000 16658464559287 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111842887/5000000000 : ℝ)^8441 ≤ (6409317080479/20000000000000 : ℝ)^6393 := by
    have hnat : (2111842887 : ℕ)^8441*20000000000000^6393 ≤ 6409317080479^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111842887 5000000000 6409317080479 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479758013/10000000000 : ℝ)^8441 ≤ (138545941833/400000000000 : ℝ)^6393 := by
    have hnat : (4479758013 : ℕ)^8441*400000000000^6393 ≤ 138545941833^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479758013 10000000000 138545941833 400000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174946189/5000000000 : ℝ), (2111842887/5000000000 : ℝ), (4479758013/10000000000 : ℝ)] ![(16658464559287/50000000000000 : ℝ), (6409317080479/20000000000000 : ℝ), (138545941833/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174946189/5000000000 : ℝ)|^8441 ≤ (16658464559287/50000000000000 : ℝ)^6393
        have hw : |(2174946189/5000000000 : ℝ)|=(2174946189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111842887/5000000000 : ℝ)|^8441 ≤ (6409317080479/20000000000000 : ℝ)^6393
        have hw : |(2111842887/5000000000 : ℝ)|=(2111842887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479758013/10000000000 : ℝ)|^8441 ≤ (138545941833/400000000000 : ℝ)^6393
        have hw : |(4479758013/10000000000 : ℝ)|=(4479758013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_4 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058554783/5000000000 : ℝ)*x 0 + (5266502647/10000000000 : ℝ)*x 1 + (5391940461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058554783/5000000000 : ℝ)^8441 ≤ (1287493227669/10000000000000 : ℝ)^6393 := by
    have hnat : (1058554783 : ℕ)^8441*10000000000000^6393 ≤ 1287493227669^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058554783 5000000000 1287493227669 10000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266502647/10000000000 : ℝ)^8441 ≤ (8577127515107/20000000000000 : ℝ)^6393 := by
    have hnat : (5266502647 : ℕ)^8441*20000000000000^6393 ≤ 8577127515107^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266502647 10000000000 8577127515107 20000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391940461/10000000000 : ℝ)^8441 ≤ (22119715072001/50000000000000 : ℝ)^6393 := by
    have hnat : (5391940461 : ℕ)^8441*50000000000000^6393 ≤ 22119715072001^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391940461 10000000000 22119715072001 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058554783/5000000000 : ℝ), (5266502647/10000000000 : ℝ), (5391940461/10000000000 : ℝ)] ![(1287493227669/10000000000000 : ℝ), (8577127515107/20000000000000 : ℝ), (22119715072001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058554783/5000000000 : ℝ)|^8441 ≤ (1287493227669/10000000000000 : ℝ)^6393
        have hw : |(-1058554783/5000000000 : ℝ)|=(1058554783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266502647/10000000000 : ℝ)|^8441 ≤ (8577127515107/20000000000000 : ℝ)^6393
        have hw : |(5266502647/10000000000 : ℝ)|=(5266502647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391940461/10000000000 : ℝ)|^8441 ≤ (22119715072001/50000000000000 : ℝ)^6393
        have hw : |(5391940461/10000000000 : ℝ)|=(5391940461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_5 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328097783/2500000000 : ℝ)*x 0 + (-1027643577/5000000000 : ℝ)*x 1 + (5391940459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328097783/2500000000 : ℝ)^8441 ≤ (43379705875753/100000000000000 : ℝ)^6393 := by
    have hnat : (1328097783 : ℕ)^8441*100000000000000^6393 ≤ 43379705875753^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328097783 2500000000 43379705875753 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027643577/5000000000 : ℝ)^8441 ≤ (386901999401/3125000000000 : ℝ)^6393 := by
    have hnat : (1027643577 : ℕ)^8441*3125000000000^6393 ≤ 386901999401^6393*5000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027643577 5000000000 386901999401 3125000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391940459/10000000000 : ℝ)^8441 ≤ (1382482191323/3125000000000 : ℝ)^6393 := by
    have hnat : (5391940459 : ℕ)^8441*3125000000000^6393 ≤ 1382482191323^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391940459 10000000000 1382482191323 3125000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328097783/2500000000 : ℝ), (-1027643577/5000000000 : ℝ), (5391940459/10000000000 : ℝ)] ![(43379705875753/100000000000000 : ℝ), (386901999401/3125000000000 : ℝ), (1382482191323/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328097783/2500000000 : ℝ)|^8441 ≤ (43379705875753/100000000000000 : ℝ)^6393
        have hw : |(1328097783/2500000000 : ℝ)|=(1328097783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1027643577/5000000000 : ℝ)|^8441 ≤ (386901999401/3125000000000 : ℝ)^6393
        have hw : |(-1027643577/5000000000 : ℝ)|=(1027643577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391940459/10000000000 : ℝ)|^8441 ≤ (1382482191323/3125000000000 : ℝ)^6393
        have hw : |(5391940459/10000000000 : ℝ)|=(5391940459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_6 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312391137/10000000000 : ℝ)*x 0 + (1078388091/2000000000 : ℝ)*x 1 + (-2055287153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312391137/10000000000 : ℝ)^8441 ≤ (21689852964831/50000000000000 : ℝ)^6393 := by
    have hnat : (5312391137 : ℕ)^8441*50000000000000^6393 ≤ 21689852964831^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312391137 10000000000 21689852964831 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078388091/2000000000 : ℝ)^8441 ≤ (44239430079003/100000000000000 : ℝ)^6393 := by
    have hnat : (1078388091 : ℕ)^8441*100000000000000^6393 ≤ 44239430079003^6393*2000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078388091 2000000000 44239430079003 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055287153/10000000000 : ℝ)^8441 ≤ (12380863972879/100000000000000 : ℝ)^6393 := by
    have hnat : (2055287153 : ℕ)^8441*100000000000000^6393 ≤ 12380863972879^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055287153 10000000000 12380863972879 100000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312391137/10000000000 : ℝ), (1078388091/2000000000 : ℝ), (-2055287153/10000000000 : ℝ)] ![(21689852964831/50000000000000 : ℝ), (44239430079003/100000000000000 : ℝ), (12380863972879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312391137/10000000000 : ℝ)|^8441 ≤ (21689852964831/50000000000000 : ℝ)^6393
        have hw : |(5312391137/10000000000 : ℝ)|=(5312391137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078388091/2000000000 : ℝ)|^8441 ≤ (44239430079003/100000000000000 : ℝ)^6393
        have hw : |(1078388091/2000000000 : ℝ)|=(1078388091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055287153/10000000000 : ℝ)|^8441 ≤ (12380863972879/100000000000000 : ℝ)^6393
        have hw : |(-2055287153/10000000000 : ℝ)|=(2055287153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1248_s5_7 (p : ℝ) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349902387/10000000000 : ℝ)*x 0 + (69985941/156250000 : ℝ)*x 1 + (1056086487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349902387/10000000000 : ℝ)^8441 ≤ (8329257584653/25000000000000 : ℝ)^6393 := by
    have hnat : (4349902387 : ℕ)^8441*25000000000000^6393 ≤ 8329257584653^6393*10000000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349902387 10000000000 8329257584653 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69985941/156250000 : ℝ)^8441 ≤ (8657442619071/25000000000000 : ℝ)^6393 := by
    have hnat : (69985941 : ℕ)^8441*25000000000000^6393 ≤ 8657442619071^6393*156250000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69985941 156250000 8657442619071 25000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056086487/2500000000 : ℝ)^8441 ≤ (16026599582829/50000000000000 : ℝ)^6393 := by
    have hnat : (1056086487 : ℕ)^8441*50000000000000^6393 ≤ 16026599582829^6393*2500000000^8441 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056086487 2500000000 16026599582829 50000000000000 8441 6393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8441/2048 : ℝ)) 8441 6393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349902387/10000000000 : ℝ), (69985941/156250000 : ℝ), (1056086487/2500000000 : ℝ)] ![(8329257584653/25000000000000 : ℝ), (8657442619071/25000000000000 : ℝ), (16026599582829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349902387/10000000000 : ℝ)|^8441 ≤ (8329257584653/25000000000000 : ℝ)^6393
        have hw : |(4349902387/10000000000 : ℝ)|=(4349902387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69985941/156250000 : ℝ)|^8441 ≤ (8657442619071/25000000000000 : ℝ)^6393
        have hw : |(69985941/156250000 : ℝ)|=(69985941/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056086487/2500000000 : ℝ)|^8441 ≤ (16026599582829/50000000000000 : ℝ)^6393
        have hw : |(1056086487/2500000000 : ℝ)|=(1056086487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1248_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5731/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14133/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (1055/256 : ℝ) ≤ (6401077608538967/50000000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^1055 ≤ (6401077608538967/50000000000000000000 : ℝ)^256 := by
      have hnat : (11361 : ℕ)^1055*50000000000000000000^256 ≤ 6401077608538967^256*100000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 6401077608538967 50000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (6401077608538967/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (1055/256 : ℝ) ≤ (32445779306519677/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^1055 ≤ (32445779306519677/100000000000000000000 : ℝ)^256 := by
      have hnat : (14237 : ℕ)^1055*100000000000000000000^256 ≤ 32445779306519677^256*100000^1055 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 32445779306519677 100000000000000000000 1055 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (32445779306519677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006401077608538967/25000000000000000000 : ℝ) ≤ (10000621238677217/10000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (25006401077608538967/25000000000000000000 : ℝ)^256 ≤ (10000621238677217/10000000000000000 : ℝ)^1055 := by
      have hnat : (25006401077608538967 : ℕ)^256*10000000000000000^1055 ≤ 10000621238677217^1055*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006401077608538967 25000000000000000000 10000621238677217 10000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000621238677217/10000000000000000 : ℝ)) (X := (25006401077608538967/25000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045247934523597611/100000000000000000000 : ℝ) ≤ (2500274442820669/2500000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (100045247934523597611/100000000000000000000 : ℝ)^256 ≤ (2500274442820669/2500000000000000 : ℝ)^1055 := by
      have hnat : (100045247934523597611 : ℕ)^256*2500000000000000^1055 ≤ 2500274442820669^1055*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045247934523597611 100000000000000000000 2500274442820669 2500000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500274442820669/2500000000000000 : ℝ)) (X := (100045247934523597611/100000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032445779306519677/50000000000000000000 : ℝ) ≤ (2000314860777627/2000000000000000 : ℝ) ^ (1055/256 : ℝ) := by
    have hpowers : (50032445779306519677/50000000000000000000 : ℝ)^256 ≤ (2000314860777627/2000000000000000 : ℝ)^1055 := by
      have hnat : (50032445779306519677 : ℕ)^256*2000000000000000^1055 ≤ 2000314860777627^1055*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032445779306519677 50000000000000000000 2000314860777627 2000000000000000 256 1055 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000314860777627/2000000000000000 : ℝ)) (X := (50032445779306519677/50000000000000000000 : ℝ)) (by norm_num) 1055 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6401077608538967/50000000000000000000 : ℝ) ≤ ((14375479454287218347/14380000000000000000 : ℝ)+2*(476532605459/287600000000000 : ℝ)*(11361/100000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (14375479454287218347/14380000000000000000 : ℝ)+2*(476532605459/287600000000000 : ℝ)*(11361/100000 : ℝ)=(10000621238677217/10000000000000000 : ℝ) by norm_num, show 1+2*(6401077608538967/50000000000000000000 : ℝ)=(25006401077608538967/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32445779306519677/100000000000000000000 : ℝ)+(6401077608538967/50000000000000000000 : ℝ) ≤ ((14375479454287218347/14380000000000000000 : ℝ)+(476532605459/287600000000000 : ℝ)*((14237/100000 : ℝ)+(11361/100000 : ℝ)))^(1055/256 : ℝ) := by
    rw [show (14375479454287218347/14380000000000000000 : ℝ)+(476532605459/287600000000000 : ℝ)*((14237/100000 : ℝ)+(11361/100000 : ℝ))=(2500274442820669/2500000000000000 : ℝ) by norm_num, show 1+(32445779306519677/100000000000000000000 : ℝ)+(6401077608538967/50000000000000000000 : ℝ)=(100045247934523597611/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32445779306519677/100000000000000000000 : ℝ) ≤ ((14375479454287218347/14380000000000000000 : ℝ)+2*(476532605459/287600000000000 : ℝ)*(14237/100000 : ℝ))^(1055/256 : ℝ) := by
    rw [show (14375479454287218347/14380000000000000000 : ℝ)+2*(476532605459/287600000000000 : ℝ)*(14237/100000 : ℝ)=(2000314860777627/2000000000000000 : ℝ) by norm_num, show 1+2*(32445779306519677/100000000000000000000 : ℝ)=(50032445779306519677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14375479454287218347/14380000000000000000 : ℝ)*(X 1 0+X 2 0)+(476532605459/287600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14375479454287218347/14380000000000000000 : ℝ)) (alpha := (476532605459/287600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14375479454287218347/14380000000000000000 : ℝ)*(X 0 1+X 2 1)+(476532605459/287600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14375479454287218347/14380000000000000000 : ℝ)) (alpha := (476532605459/287600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14375479454287218347/14380000000000000000 : ℝ)*(X 0 2+X 1 2)+(476532605459/287600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1055/256 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (14375479454287218347/14380000000000000000 : ℝ)) (alpha := (476532605459/287600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-52927617/250000000 : ℝ)*X 0 0+(5392265573/10000000000 : ℝ)*X 0 1+(1053235743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672287713/5000000000 : ℝ)*X 1 0+(-2181048907/10000000000 : ℝ)*X 1 1+(210647149/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672287727/5000000000 : ℝ)*X 2 0+(5266178731/10000000000 : ℝ)*X 2 1+(-2181048861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174946189/5000000000 : ℝ)*X 0 0+(2111842887/5000000000 : ℝ)*X 0 1+(4479758013/10000000000 : ℝ)*X 0 2+(2174946189/5000000000 : ℝ)*X 1 0+(2111842887/5000000000 : ℝ)*X 1 1+(4479758013/10000000000 : ℝ)*X 1 2+(2174946189/5000000000 : ℝ)*X 2 0+(2111842887/5000000000 : ℝ)*X 2 1+(4479758013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058554783/5000000000 : ℝ)*X 0 0+(5266502647/10000000000 : ℝ)*X 0 1+(5391940461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328097783/2500000000 : ℝ)*X 1 0+(-1027643577/5000000000 : ℝ)*X 1 1+(5391940459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312391137/10000000000 : ℝ)*X 2 0+(1078388091/2000000000 : ℝ)*X 2 1+(-2055287153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349902387/10000000000 : ℝ)*X 0 0+(69985941/156250000 : ℝ)*X 0 1+(1056086487/2500000000 : ℝ)*X 0 2+(4349902387/10000000000 : ℝ)*X 1 0+(69985941/156250000 : ℝ)*X 1 1+(1056086487/2500000000 : ℝ)*X 1 2+(4349902387/10000000000 : ℝ)*X 2 0+(69985941/156250000 : ℝ)*X 2 1+(1056086487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1248_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277266886500903063148710429/89875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143287387/25000000000000 : ℝ)*(base19) + (59621313/10000000000000 : ℝ)*(base23) + (7138851/25000000000000 : ℝ)*(upper3) + (9880507/100000000000000 : ℝ)*(upper4) + (12109887/12500000000000 : ℝ)*(upper5) + (739764929531331/12500000000000 : ℝ)*(major0) + (739764929531331/12500000000000 : ℝ)*(major1) + (739764929531331/12500000000000 : ℝ)*(major2) + (7931056335905751/100000000000000 : ℝ)*(sp0) + (1586215139366493/20000000000000 : ℝ)*(sp1) + (7931075673768883/100000000000000 : ℝ)*(sp2) + (1952577885834927/50000000000000 : ℝ)*(sp3) + (9967038131/50000000000000 : ℝ)*(sp4) + (3364007579/50000000000000 : ℝ)*(sp7) + (976290624921253/25000000000000 : ℝ)*(f.failure) + (7931076269982013/100000000000000 : ℝ)*(f.sum) + (2241819346953/898750000000000000000000000 : ℝ)*base66 + (1259874792727229857/179750000000000000000000000000000 : ℝ)*base67 + (296447433889229857/179750000000000000000000000000000 : ℝ)*base69 + (1456587472542979857/179750000000000000000000000000000 : ℝ)*base71 + (12535608826223/3595000000000000000000000000 : ℝ)*base73 + (1711823889056270143/179750000000000000000000000000000 : ℝ)*base76 + (2306302968180979857/179750000000000000000000000000000 : ℝ)*base77 + (2703855663843770143/179750000000000000000000000000000 : ℝ)*base80 + (1408217467173/3595000000000000000000000000 : ℝ)*base81 + (52471/39062500000000000000 : ℝ)*base89 + (52471/39062500000000000000 : ℝ)*base91 + (52471/39062500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3353515035730177336126198599/359500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1667160139/100000000000000 : ℝ)*(base19) + (113967079/6250000000000 : ℝ)*(base23) + (93014221/50000000000000 : ℝ)*(upper3) + (67744423/100000000000000 : ℝ)*(lower4) + (19266013/10000000000000 : ℝ)*(upper5) + (2974356765575987/50000000000000 : ℝ)*(major0) + (2974356765575987/50000000000000 : ℝ)*(major1) + (2974356765575987/50000000000000 : ℝ)*(major2) + (11541954019/25000000000000 : ℝ)*(sp1) + (1552552001/3125000000000 : ℝ)*(sp2) + (797207626571103/10000000000000 : ℝ)*(sp4) + (1594405686146963/20000000000000 : ℝ)*(sp5) + (3986012380286867/50000000000000 : ℝ)*(sp6) + (392535048565039/10000000000000 : ℝ)*(sp7) + (392535048565039/10000000000000 : ℝ)*(f.failure) + (797207626571103/10000000000000 : ℝ)*(f.sum) + (19908136047467/7190000000000000000000000000 : ℝ)*base66 + (2012960944510683489/719000000000000000000000000000000 : ℝ)*base67 + (12057376003690683489/719000000000000000000000000000000 : ℝ)*base69 + (3850648647106683489/719000000000000000000000000000000 : ℝ)*base71 + (49703668377387/7190000000000000000000000000 : ℝ)*base74 + (6555891166445683489/719000000000000000000000000000000 : ℝ)*base75 + (2763910970636683489/719000000000000000000000000000000 : ℝ)*base77 + (18881408475022683489/719000000000000000000000000000000 : ℝ)*base79 + (18898982993507/7190000000000000000000000000 : ℝ)*base82 + (134127/15625000000000000000 : ℝ)*base90 + (134127/15625000000000000000 : ℝ)*base92 + (134127/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1248_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1248_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1248_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1248_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1248_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1248_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1055/256 : ℝ) ≤ p) (hpb : p ≤ (8441/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2367907/1562500 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1013/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9523/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1248_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
