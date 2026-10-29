-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1600_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:33.595915+00:00
-- url     : https://prove2.me/submissions/c2496b6f-69c8-4eb0-82d0-969cfc91b12f

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
theorem support_rectangle_w1600_s3_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-172962513/1000000000 : ℝ)*x 0 + (136582443/250000000 : ℝ)*x 1 + (323695283/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172962513/1000000000 : ℝ)^4719 ≤ (531783264781/5000000000000 : ℝ)^3695 := by
    have hnat : (172962513 : ℕ)^4719*5000000000000^3695 ≤ 531783264781^3695*1000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172962513 1000000000 531783264781 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136582443/250000000 : ℝ)^4719 ≤ (462056841403/1000000000000 : ℝ)^3695 := by
    have hnat : (136582443 : ℕ)^4719*1000000000000^3695 ≤ 462056841403^3695*250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136582443 250000000 462056841403 1000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323695283/625000000 : ℝ)^4719 ≤ (43158650548807/100000000000000 : ℝ)^3695 := by
    have hnat : (323695283 : ℕ)^4719*100000000000000^3695 ≤ 43158650548807^3695*625000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323695283 625000000 43158650548807 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-172962513/1000000000 : ℝ), (136582443/250000000 : ℝ), (323695283/625000000 : ℝ)] ![(531783264781/5000000000000 : ℝ), (462056841403/1000000000000 : ℝ), (43158650548807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-172962513/1000000000 : ℝ)|^4719 ≤ (531783264781/5000000000000 : ℝ)^3695
        have hw : |(-172962513/1000000000 : ℝ)|=(172962513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136582443/250000000 : ℝ)|^4719 ≤ (462056841403/1000000000000 : ℝ)^3695
        have hw : |(136582443/250000000 : ℝ)|=(136582443/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323695283/625000000 : ℝ)|^4719 ≤ (43158650548807/100000000000000 : ℝ)^3695
        have hw : |(323695283/625000000 : ℝ)|=(323695283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107103369/200000000 : ℝ)*x 0 + (-1876247733/10000000000 : ℝ)*x 1 + (647390551/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107103369/200000000 : ℝ)^4719 ≤ (22520482896823/50000000000000 : ℝ)^3695 := by
    have hnat : (107103369 : ℕ)^4719*50000000000000^3695 ≤ 22520482896823^3695*200000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107103369 200000000 22520482896823 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876247733/10000000000 : ℝ)^4719 ≤ (5900192457187/50000000000000 : ℝ)^3695 := by
    have hnat : (1876247733 : ℕ)^4719*50000000000000^3695 ≤ 5900192457187^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876247733 10000000000 5900192457187 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647390551/1250000000 : ℝ)^4719 ≤ (43158649271697/100000000000000 : ℝ)^3695 := by
    have hnat : (647390551 : ℕ)^4719*100000000000000^3695 ≤ 43158649271697^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647390551 1250000000 43158649271697 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107103369/200000000 : ℝ), (-1876247733/10000000000 : ℝ), (647390551/1250000000 : ℝ)] ![(22520482896823/50000000000000 : ℝ), (5900192457187/50000000000000 : ℝ), (43158649271697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107103369/200000000 : ℝ)|^4719 ≤ (22520482896823/50000000000000 : ℝ)^3695
        have hw : |(107103369/200000000 : ℝ)|=(107103369/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1876247733/10000000000 : ℝ)|^4719 ≤ (5900192457187/50000000000000 : ℝ)^3695
        have hw : |(-1876247733/10000000000 : ℝ)|=(1876247733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647390551/1250000000 : ℝ)|^4719 ≤ (43158649271697/100000000000000 : ℝ)^3695
        have hw : |(647390551/1250000000 : ℝ)|=(647390551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071033763/2000000000 : ℝ)*x 0 + (1035824823/2000000000 : ℝ)*x 1 + (-1876247633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071033763/2000000000 : ℝ)^4719 ≤ (2252048485717/5000000000000 : ℝ)^3695 := by
    have hnat : (1071033763 : ℕ)^4719*5000000000000^3695 ≤ 2252048485717^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071033763 2000000000 2252048485717 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035824823/2000000000 : ℝ)^4719 ≤ (2157932307671/5000000000000 : ℝ)^3695 := by
    have hnat : (1035824823 : ℕ)^4719*5000000000000^3695 ≤ 2157932307671^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035824823 2000000000 2157932307671 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876247633/10000000000 : ℝ)^4719 ≤ (11800384111141/100000000000000 : ℝ)^3695 := by
    have hnat : (1876247633 : ℕ)^4719*100000000000000^3695 ≤ 11800384111141^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876247633 10000000000 11800384111141 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071033763/2000000000 : ℝ), (1035824823/2000000000 : ℝ), (-1876247633/10000000000 : ℝ)] ![(2252048485717/5000000000000 : ℝ), (2157932307671/5000000000000 : ℝ), (11800384111141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071033763/2000000000 : ℝ)|^4719 ≤ (2252048485717/5000000000000 : ℝ)^3695
        have hw : |(1071033763/2000000000 : ℝ)|=(1071033763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035824823/2000000000 : ℝ)|^4719 ≤ (2157932307671/5000000000000 : ℝ)^3695
        have hw : |(1035824823/2000000000 : ℝ)|=(1035824823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876247633/10000000000 : ℝ)|^4719 ≤ (11800384111141/100000000000000 : ℝ)^3695
        have hw : |(-1876247633/10000000000 : ℝ)|=(1876247633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4220767979/10000000000 : ℝ)*x 0 + (3887203903/10000000000 : ℝ)*x 1 + (228816467/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220767979/10000000000 : ℝ)^4719 ≤ (33233474492381/100000000000000 : ℝ)^3695 := by
    have hnat : (4220767979 : ℕ)^4719*100000000000000^3695 ≤ 33233474492381^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220767979 10000000000 33233474492381 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3887203903/10000000000 : ℝ)^4719 ≤ (934895390393/3125000000000 : ℝ)^3695 := by
    have hnat : (3887203903 : ℕ)^4719*3125000000000^3695 ≤ 934895390393^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3887203903 10000000000 934895390393 3125000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228816467/500000000 : ℝ)^4719 ≤ (8996551027/24414062500 : ℝ)^3695 := by
    have hnat : (228816467 : ℕ)^4719*24414062500^3695 ≤ 8996551027^3695*500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228816467 500000000 8996551027 24414062500 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220767979/10000000000 : ℝ), (3887203903/10000000000 : ℝ), (228816467/500000000 : ℝ)] ![(33233474492381/100000000000000 : ℝ), (934895390393/3125000000000 : ℝ), (8996551027/24414062500 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220767979/10000000000 : ℝ)|^4719 ≤ (33233474492381/100000000000000 : ℝ)^3695
        have hw : |(4220767979/10000000000 : ℝ)|=(4220767979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3887203903/10000000000 : ℝ)|^4719 ≤ (934895390393/3125000000000 : ℝ)^3695
        have hw : |(3887203903/10000000000 : ℝ)|=(3887203903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228816467/500000000 : ℝ)|^4719 ≤ (8996551027/24414062500 : ℝ)^3695
        have hw : |(228816467/500000000 : ℝ)|=(228816467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-432424613/2500000000 : ℝ)*x 0 + (207249491/400000000 : ℝ)*x 1 + (218446499/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432424613/2500000000 : ℝ)^4719 ≤ (1063624111339/10000000000000 : ℝ)^3695 := by
    have hnat : (432424613 : ℕ)^4719*10000000000000^3695 ≤ 1063624111339^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432424613 2500000000 1063624111339 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207249491/400000000 : ℝ)^4719 ≤ (2159056845229/5000000000000 : ℝ)^3695 := by
    have hnat : (207249491 : ℕ)^4719*5000000000000^3695 ≤ 2159056845229^3695*400000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207249491 400000000 2159056845229 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218446499/400000000 : ℝ)^4719 ≤ (11545655491333/25000000000000 : ℝ)^3695 := by
    have hnat : (218446499 : ℕ)^4719*25000000000000^3695 ≤ 11545655491333^3695*400000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218446499 400000000 11545655491333 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432424613/2500000000 : ℝ), (207249491/400000000 : ℝ), (218446499/400000000 : ℝ)] ![(1063624111339/10000000000000 : ℝ), (2159056845229/5000000000000 : ℝ), (11545655491333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432424613/2500000000 : ℝ)|^4719 ≤ (1063624111339/10000000000000 : ℝ)^3695
        have hw : |(-432424613/2500000000 : ℝ)|=(432424613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207249491/400000000 : ℝ)|^4719 ≤ (2159056845229/5000000000000 : ℝ)^3695
        have hw : |(207249491/400000000 : ℝ)|=(207249491/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218446499/400000000 : ℝ)|^4719 ≤ (11545655491333/25000000000000 : ℝ)^3695
        have hw : |(218446499/400000000 : ℝ)|=(218446499/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279840007/10000000000 : ℝ)*x 0 + (-1594209543/10000000000 : ℝ)*x 1 + (5461162639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279840007/10000000000 : ℝ)^4719 ≤ (8846679645761/20000000000000 : ℝ)^3695 := by
    have hnat : (5279840007 : ℕ)^4719*20000000000000^3695 ≤ 8846679645761^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279840007 10000000000 8846679645761 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1594209543/10000000000 : ℝ)^4719 ≤ (9583978016967/100000000000000 : ℝ)^3695 := by
    have hnat : (1594209543 : ℕ)^4719*100000000000000^3695 ≤ 9583978016967^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594209543 10000000000 9583978016967 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5461162639/10000000000 : ℝ)^4719 ≤ (46182623736553/100000000000000 : ℝ)^3695 := by
    have hnat : (5461162639 : ℕ)^4719*100000000000000^3695 ≤ 46182623736553^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461162639 10000000000 46182623736553 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279840007/10000000000 : ℝ), (-1594209543/10000000000 : ℝ), (5461162639/10000000000 : ℝ)] ![(8846679645761/20000000000000 : ℝ), (9583978016967/100000000000000 : ℝ), (46182623736553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279840007/10000000000 : ℝ)|^4719 ≤ (8846679645761/20000000000000 : ℝ)^3695
        have hw : |(5279840007/10000000000 : ℝ)|=(5279840007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1594209543/10000000000 : ℝ)|^4719 ≤ (9583978016967/100000000000000 : ℝ)^3695
        have hw : |(-1594209543/10000000000 : ℝ)|=(1594209543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5461162639/10000000000 : ℝ)|^4719 ≤ (46182623736553/100000000000000 : ℝ)^3695
        have hw : |(5461162639/10000000000 : ℝ)|=(5461162639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329990013/625000000 : ℝ)*x 0 + (5461162389/10000000000 : ℝ)*x 1 + (-99638101/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329990013/625000000 : ℝ)^4719 ≤ (44233400379413/100000000000000 : ℝ)^3695 := by
    have hnat : (329990013 : ℕ)^4719*100000000000000^3695 ≤ 44233400379413^3695*625000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329990013 625000000 44233400379413 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5461162389/10000000000 : ℝ)^4719 ≤ (46182621036521/100000000000000 : ℝ)^3695 := by
    have hnat : (5461162389 : ℕ)^4719*100000000000000^3695 ≤ 46182621036521^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5461162389 10000000000 46182621036521 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99638101/625000000 : ℝ)^4719 ≤ (1916795715489/20000000000000 : ℝ)^3695 := by
    have hnat : (99638101 : ℕ)^4719*20000000000000^3695 ≤ 1916795715489^3695*625000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99638101 625000000 1916795715489 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329990013/625000000 : ℝ), (5461162389/10000000000 : ℝ), (-99638101/625000000 : ℝ)] ![(44233400379413/100000000000000 : ℝ), (46182621036521/100000000000000 : ℝ), (1916795715489/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329990013/625000000 : ℝ)|^4719 ≤ (44233400379413/100000000000000 : ℝ)^3695
        have hw : |(329990013/625000000 : ℝ)|=(329990013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5461162389/10000000000 : ℝ)|^4719 ≤ (46182621036521/100000000000000 : ℝ)^3695
        have hw : |(5461162389/10000000000 : ℝ)|=(5461162389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99638101/625000000 : ℝ)|^4719 ≤ (1916795715489/20000000000000 : ℝ)^3695
        have hw : |(-99638101/625000000 : ℝ)|=(99638101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s3_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4220944909/10000000000 : ℝ)*x 0 + (4571205101/10000000000 : ℝ)*x 1 + (3892382429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220944909/10000000000 : ℝ)^4719 ≤ (33235253688423/100000000000000 : ℝ)^3695 := by
    have hnat : (4220944909 : ℕ)^4719*100000000000000^3695 ≤ 33235253688423^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220944909 10000000000 33235253688423 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4571205101/10000000000 : ℝ)^4719 ≤ (18398592229341/50000000000000 : ℝ)^3695 := by
    have hnat : (4571205101 : ℕ)^4719*50000000000000^3695 ≤ 18398592229341^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571205101 10000000000 18398592229341 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3892382429/10000000000 : ℝ)^4719 ≤ (14983780918623/50000000000000 : ℝ)^3695 := by
    have hnat : (3892382429 : ℕ)^4719*50000000000000^3695 ≤ 14983780918623^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3892382429 10000000000 14983780918623 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220944909/10000000000 : ℝ), (4571205101/10000000000 : ℝ), (3892382429/10000000000 : ℝ)] ![(33235253688423/100000000000000 : ℝ), (18398592229341/50000000000000 : ℝ), (14983780918623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220944909/10000000000 : ℝ)|^4719 ≤ (33235253688423/100000000000000 : ℝ)^3695
        have hw : |(4220944909/10000000000 : ℝ)|=(4220944909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4571205101/10000000000 : ℝ)|^4719 ≤ (18398592229341/50000000000000 : ℝ)^3695
        have hw : |(4571205101/10000000000 : ℝ)|=(4571205101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3892382429/10000000000 : ℝ)|^4719 ≤ (14983780918623/50000000000000 : ℝ)^3695
        have hw : |(3892382429/10000000000 : ℝ)|=(3892382429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8187/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8269/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5103/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8269/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5103/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8269/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5103/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8269/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5103/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8269/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5103/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8269/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5103/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5103/50000 : ℝ) ^ (4715/1024 : ℝ) ≤ (2730757830885781/100000000000000000000 : ℝ) := by
    have hpowers : (5103/50000 : ℝ)^4715 ≤ (2730757830885781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5103 : ℕ)^4715*100000000000000000000^1024 ≤ 2730757830885781^1024*50000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5103 50000 2730757830885781 100000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5103/50000 : ℝ)) (X := (2730757830885781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8269/50000 : ℝ) ^ (4715/1024 : ℝ) ≤ (12603205751387103/50000000000000000000 : ℝ) := by
    have hpowers : (8269/50000 : ℝ)^4715 ≤ (12603205751387103/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8269 : ℕ)^4715*50000000000000000000^1024 ≤ 12603205751387103^1024*50000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8269 50000 12603205751387103 50000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8269/50000 : ℝ)) (X := (12603205751387103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002730757830885781/50000000000000000000 : ℝ) ≤ (5000059305116533/5000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (50002730757830885781/50000000000000000000 : ℝ)^1024 ≤ (5000059305116533/5000000000000000 : ℝ)^4715 := by
      have hnat : (50002730757830885781 : ℕ)^1024*5000000000000000^4715 ≤ 5000059305116533^4715*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002730757830885781 50000000000000000000 5000059305116533 5000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000059305116533/5000000000000000 : ℝ)) (X := (50002730757830885781/50000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027937169333659987/100000000000000000000 : ℝ) ≤ (10000606670916187/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (100027937169333659987/100000000000000000000 : ℝ)^1024 ≤ (10000606670916187/10000000000000000 : ℝ)^4715 := by
      have hnat : (100027937169333659987 : ℕ)^1024*10000000000000000^4715 ≤ 10000606670916187^4715*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027937169333659987 100000000000000000000 10000606670916187 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000606670916187/10000000000000000 : ℝ)) (X := (100027937169333659987/100000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012603205751387103/25000000000000000000 : ℝ) ≤ (2500273682899827/2500000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (25012603205751387103/25000000000000000000 : ℝ)^1024 ≤ (2500273682899827/2500000000000000 : ℝ)^4715 := by
      have hnat : (25012603205751387103 : ℕ)^1024*2500000000000000^4715 ≤ 2500273682899827^4715*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012603205751387103 25000000000000000000 2500273682899827 2500000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500273682899827/2500000000000000 : ℝ)) (X := (25012603205751387103/25000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2730757830885781/100000000000000000000 : ℝ) ≤ ((3165539437266595403/3166000000000000000 : ℝ)+2*(488060683121/633200000000000 : ℝ)*(5103/50000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (3165539437266595403/3166000000000000000 : ℝ)+2*(488060683121/633200000000000 : ℝ)*(5103/50000 : ℝ)=(5000059305116533/5000000000000000 : ℝ) by norm_num, show 1+2*(2730757830885781/100000000000000000000 : ℝ)=(50002730757830885781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12603205751387103/50000000000000000000 : ℝ)+(2730757830885781/100000000000000000000 : ℝ) ≤ ((3165539437266595403/3166000000000000000 : ℝ)+(488060683121/633200000000000 : ℝ)*((8269/50000 : ℝ)+(5103/50000 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (3165539437266595403/3166000000000000000 : ℝ)+(488060683121/633200000000000 : ℝ)*((8269/50000 : ℝ)+(5103/50000 : ℝ))=(10000606670916187/10000000000000000 : ℝ) by norm_num, show 1+(12603205751387103/50000000000000000000 : ℝ)+(2730757830885781/100000000000000000000 : ℝ)=(100027937169333659987/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12603205751387103/50000000000000000000 : ℝ) ≤ ((3165539437266595403/3166000000000000000 : ℝ)+2*(488060683121/633200000000000 : ℝ)*(8269/50000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (3165539437266595403/3166000000000000000 : ℝ)+2*(488060683121/633200000000000 : ℝ)*(8269/50000 : ℝ)=(2500273682899827/2500000000000000 : ℝ) by norm_num, show 1+2*(12603205751387103/50000000000000000000 : ℝ)=(25012603205751387103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3165539437266595403/3166000000000000000 : ℝ)*(X 1 0+X 2 0)+(488060683121/633200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (5103/50000 : ℝ)) (hi := (8269/50000 : ℝ)) (c := (3165539437266595403/3166000000000000000 : ℝ)) (alpha := (488060683121/633200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3165539437266595403/3166000000000000000 : ℝ)*(X 0 1+X 2 1)+(488060683121/633200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (5103/50000 : ℝ)) (hi := (8269/50000 : ℝ)) (c := (3165539437266595403/3166000000000000000 : ℝ)) (alpha := (488060683121/633200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3165539437266595403/3166000000000000000 : ℝ)*(X 0 2+X 1 2)+(488060683121/633200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (5103/50000 : ℝ)) (hi := (8269/50000 : ℝ)) (c := (3165539437266595403/3166000000000000000 : ℝ)) (alpha := (488060683121/633200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-172962513/1000000000 : ℝ)*X 0 0+(136582443/250000000 : ℝ)*X 0 1+(323695283/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107103369/200000000 : ℝ)*X 1 0+(-1876247733/10000000000 : ℝ)*X 1 1+(647390551/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071033763/2000000000 : ℝ)*X 2 0+(1035824823/2000000000 : ℝ)*X 2 1+(-1876247633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4220767979/10000000000 : ℝ)*X 0 0+(3887203903/10000000000 : ℝ)*X 0 1+(228816467/500000000 : ℝ)*X 0 2+(4220767979/10000000000 : ℝ)*X 1 0+(3887203903/10000000000 : ℝ)*X 1 1+(228816467/500000000 : ℝ)*X 1 2+(4220767979/10000000000 : ℝ)*X 2 0+(3887203903/10000000000 : ℝ)*X 2 1+(228816467/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432424613/2500000000 : ℝ)*X 0 0+(207249491/400000000 : ℝ)*X 0 1+(218446499/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279840007/10000000000 : ℝ)*X 1 0+(-1594209543/10000000000 : ℝ)*X 1 1+(5461162639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329990013/625000000 : ℝ)*X 2 0+(5461162389/10000000000 : ℝ)*X 2 1+(-99638101/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4220944909/10000000000 : ℝ)*X 0 0+(4571205101/10000000000 : ℝ)*X 0 1+(3892382429/10000000000 : ℝ)*X 0 2+(4220944909/10000000000 : ℝ)*X 1 0+(4571205101/10000000000 : ℝ)*X 1 1+(3892382429/10000000000 : ℝ)*X 1 2+(4220944909/10000000000 : ℝ)*X 2 0+(4571205101/10000000000 : ℝ)*X 2 1+(3892382429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201138728407789771655472819/39575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52322149/6250000000000 : ℝ)*(base19) + (165990171/20000000000000 : ℝ)*(base23) + (16537617/12500000000000 : ℝ)*(lower2) + (126671703/100000000000000 : ℝ)*(upper3) + (55695371/100000000000000 : ℝ)*(upper5) + (1242529845521791/50000000000000 : ℝ)*(major0) + (1242529845521791/50000000000000 : ℝ)*(major1) + (1242529845521791/50000000000000 : ℝ)*(major2) + (1759493860369041/50000000000000 : ℝ)*(sp0) + (1759497602261401/50000000000000 : ℝ)*(sp1) + (351899521172633/10000000000000 : ℝ)*(sp2) + (145111809953037/10000000000000 : ℝ)*(sp3) + (8320939103/100000000000000 : ℝ)*(sp4) + (5071463951/100000000000000 : ℝ)*(sp7) + (725561585497161/50000000000000 : ℝ)*(f.failure) + (1759498020838593/50000000000000 : ℝ)*(f.sum) + (50027163662121/15830000000000000000000000000 : ℝ)*base65 + (166609174799681773/158300000000000000000000000000000 : ℝ)*base67 + (683259592834518227/158300000000000000000000000000000 : ℝ)*base70 + (916797459873218227/158300000000000000000000000000000 : ℝ)*base72 + (64011198519861/15830000000000000000000000000 : ℝ)*base73 + (1477469054843018227/158300000000000000000000000000000 : ℝ)*base76 + (624639304388218227/158300000000000000000000000000000 : ℝ)*base78 + (293570600805818227/158300000000000000000000000000000 : ℝ)*base80 + (6317883466841/15830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (8380867/625000000000000000000 : ℝ)*base89 + (8380867/625000000000000000000 : ℝ)*base91 + (8380867/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (453896487770915102781838131/79150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104770349/12500000000000 : ℝ)*(base19) + (975211827/100000000000000 : ℝ)*(base23) + (30120977/25000000000000 : ℝ)*(upper3) + (1050417/12500000000000 : ℝ)*(lower4) + (76165491/50000000000000 : ℝ)*(upper5) + (1261380708146753/50000000000000 : ℝ)*(major0) + (1261380708146753/50000000000000 : ℝ)*(major1) + (1261380708146753/50000000000000 : ℝ)*(major2) + (11293917363/100000000000000 : ℝ)*(sp1) + (10251986373/100000000000000 : ℝ)*(sp2) + (893095991053387/25000000000000 : ℝ)*(sp4) + (1786185916066697/50000000000000 : ℝ)*(sp5) + (893093184253837/25000000000000 : ℝ)*(sp6) + (1473138677218903/100000000000000 : ℝ)*(sp7) + (1473138677218903/100000000000000 : ℝ)*(f.failure) + (893095991053387/25000000000000 : ℝ)*(f.sum) + (50763879772383/15830000000000000000000000000 : ℝ)*base65 + (40039260165158541/158300000000000000000000000000000 : ℝ)*base68 + (474357596272358541/158300000000000000000000000000000 : ℝ)*base70 + (1329975309230758541/158300000000000000000000000000000 : ℝ)*base72 + (104871293865053/15830000000000000000000000000 : ℝ)*base73 + (3070659889803358541/158300000000000000000000000000000 : ℝ)*base76 + (1287452647830058541/158300000000000000000000000000000 : ℝ)*base78 + (1102458560621258541/158300000000000000000000000000000 : ℝ)*base80 + (14516713360813/15830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (7577341/1250000000000000000000 : ℝ)*base89 + (7577341/1250000000000000000000 : ℝ)*base91 + (7577341/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1600_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1600_s4_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-172977287/1000000000 : ℝ)*x 0 + (2731282273/5000000000 : ℝ)*x 1 + (647469949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172977287/1000000000 : ℝ)^4719 ≤ (5318412772633/50000000000000 : ℝ)^3695 := by
    have hnat : (172977287 : ℕ)^4719*50000000000000^3695 ≤ 5318412772633^3695*1000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172977287 1000000000 5318412772633 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731282273/5000000000 : ℝ)^4719 ≤ (11549441263613/25000000000000 : ℝ)^3695 := by
    have hnat : (2731282273 : ℕ)^4719*25000000000000^3695 ≤ 11549441263613^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731282273 5000000000 11549441263613 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647469949/1250000000 : ℝ)^4719 ≤ (10791352346213/25000000000000 : ℝ)^3695 := by
    have hnat : (647469949 : ℕ)^4719*25000000000000^3695 ≤ 10791352346213^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647469949 1250000000 10791352346213 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-172977287/1000000000 : ℝ), (2731282273/5000000000 : ℝ), (647469949/1250000000 : ℝ)] ![(5318412772633/50000000000000 : ℝ), (11549441263613/25000000000000 : ℝ), (10791352346213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-172977287/1000000000 : ℝ)|^4719 ≤ (5318412772633/50000000000000 : ℝ)^3695
        have hw : |(-172977287/1000000000 : ℝ)|=(172977287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731282273/5000000000 : ℝ)|^4719 ≤ (11549441263613/25000000000000 : ℝ)^3695
        have hw : |(2731282273/5000000000 : ℝ)|=(2731282273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647469949/1250000000 : ℝ)|^4719 ≤ (10791352346213/25000000000000 : ℝ)^3695
        have hw : |(647469949/1250000000 : ℝ)|=(647469949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677486511/5000000000 : ℝ)*x 0 + (-23445843/125000000 : ℝ)*x 1 + (5179759591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677486511/5000000000 : ℝ)^4719 ≤ (22519433294729/50000000000000 : ℝ)^3695 := by
    have hnat : (2677486511 : ℕ)^4719*50000000000000^3695 ≤ 22519433294729^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677486511 5000000000 22519433294729 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23445843/125000000 : ℝ)^4719 ≤ (11795724009433/100000000000000 : ℝ)^3695 := by
    have hnat : (23445843 : ℕ)^4719*100000000000000^3695 ≤ 11795724009433^3695*125000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23445843 125000000 11795724009433 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179759591/10000000000 : ℝ)^4719 ≤ (43165409374209/100000000000000 : ℝ)^3695 := by
    have hnat : (5179759591 : ℕ)^4719*100000000000000^3695 ≤ 43165409374209^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179759591 10000000000 43165409374209 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677486511/5000000000 : ℝ), (-23445843/125000000 : ℝ), (5179759591/10000000000 : ℝ)] ![(22519433294729/50000000000000 : ℝ), (11795724009433/100000000000000 : ℝ), (43165409374209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677486511/5000000000 : ℝ)|^4719 ≤ (22519433294729/50000000000000 : ℝ)^3695
        have hw : |(2677486511/5000000000 : ℝ)|=(2677486511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23445843/125000000 : ℝ)|^4719 ≤ (11795724009433/100000000000000 : ℝ)^3695
        have hw : |(-23445843/125000000 : ℝ)|=(23445843/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179759591/10000000000 : ℝ)|^4719 ≤ (43165409374209/100000000000000 : ℝ)^3695
        have hw : |(5179759591/10000000000 : ℝ)|=(5179759591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677486511/5000000000 : ℝ)*x 0 + (647469949/1250000000 : ℝ)*x 1 + (-23445843/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677486511/5000000000 : ℝ)^4719 ≤ (22519433294729/50000000000000 : ℝ)^3695 := by
    have hnat : (2677486511 : ℕ)^4719*50000000000000^3695 ≤ 22519433294729^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677486511 5000000000 22519433294729 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647469949/1250000000 : ℝ)^4719 ≤ (10791352346213/25000000000000 : ℝ)^3695 := by
    have hnat : (647469949 : ℕ)^4719*25000000000000^3695 ≤ 10791352346213^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647469949 1250000000 10791352346213 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23445843/125000000 : ℝ)^4719 ≤ (11795724009433/100000000000000 : ℝ)^3695 := by
    have hnat : (23445843 : ℕ)^4719*100000000000000^3695 ≤ 11795724009433^3695*125000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23445843 125000000 11795724009433 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677486511/5000000000 : ℝ), (647469949/1250000000 : ℝ), (-23445843/125000000 : ℝ)] ![(22519433294729/50000000000000 : ℝ), (10791352346213/25000000000000 : ℝ), (11795724009433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677486511/5000000000 : ℝ)|^4719 ≤ (22519433294729/50000000000000 : ℝ)^3695
        have hw : |(2677486511/5000000000 : ℝ)|=(2677486511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647469949/1250000000 : ℝ)|^4719 ≤ (10791352346213/25000000000000 : ℝ)^3695
        have hw : |(647469949/1250000000 : ℝ)|=(647469949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23445843/125000000 : ℝ)|^4719 ≤ (11795724009433/100000000000000 : ℝ)^3695
        have hw : |(-23445843/125000000 : ℝ)|=(23445843/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42208631/100000000 : ℝ)*x 0 + (1944426647/5000000000 : ℝ)*x 1 + (2287329849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42208631/100000000 : ℝ)^4719 ≤ (8308607755029/25000000000000 : ℝ)^3695 := by
    have hnat : (42208631 : ℕ)^4719*25000000000000^3695 ≤ 8308607755029^3695*100000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42208631 100000000 8308607755029 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944426647/5000000000 : ℝ)^4719 ≤ (7483216344941/25000000000000 : ℝ)^3695 := by
    have hnat : (1944426647 : ℕ)^4719*25000000000000^3695 ≤ 7483216344941^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944426647 5000000000 7483216344941 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2287329849/5000000000 : ℝ)^4719 ≤ (18416351792563/50000000000000 : ℝ)^3695 := by
    have hnat : (2287329849 : ℕ)^4719*50000000000000^3695 ≤ 18416351792563^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287329849 5000000000 18416351792563 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42208631/100000000 : ℝ), (1944426647/5000000000 : ℝ), (2287329849/5000000000 : ℝ)] ![(8308607755029/25000000000000 : ℝ), (7483216344941/25000000000000 : ℝ), (18416351792563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42208631/100000000 : ℝ)|^4719 ≤ (8308607755029/25000000000000 : ℝ)^3695
        have hw : |(42208631/100000000 : ℝ)|=(42208631/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1944426647/5000000000 : ℝ)|^4719 ≤ (7483216344941/25000000000000 : ℝ)^3695
        have hw : |(1944426647/5000000000 : ℝ)|=(1944426647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2287329849/5000000000 : ℝ)|^4719 ≤ (18416351792563/50000000000000 : ℝ)^3695
        have hw : |(2287329849/5000000000 : ℝ)|=(2287329849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-86492243/500000000 : ℝ)*x 0 + (5181852407/10000000000 : ℝ)*x 1 + (1365112441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86492243/500000000 : ℝ)^4719 ≤ (10637390915797/100000000000000 : ℝ)^3695 := by
    have hnat : (86492243 : ℕ)^4719*100000000000000^3695 ≤ 10637390915797^3695*500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86492243 500000000 10637390915797 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181852407/10000000000 : ℝ)^4719 ≤ (43187684345531/100000000000000 : ℝ)^3695 := by
    have hnat : (5181852407 : ℕ)^4719*100000000000000^3695 ≤ 43187684345531^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181852407 10000000000 43187684345531 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365112441/2500000000 : ℝ)^4719 ≤ (46174924732371/100000000000000 : ℝ)^3695 := by
    have hnat : (1365112441 : ℕ)^4719*100000000000000^3695 ≤ 46174924732371^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365112441 2500000000 46174924732371 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86492243/500000000 : ℝ), (5181852407/10000000000 : ℝ), (1365112441/2500000000 : ℝ)] ![(10637390915797/100000000000000 : ℝ), (43187684345531/100000000000000 : ℝ), (46174924732371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86492243/500000000 : ℝ)|^4719 ≤ (10637390915797/100000000000000 : ℝ)^3695
        have hw : |(-86492243/500000000 : ℝ)|=(86492243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181852407/10000000000 : ℝ)|^4719 ≤ (43187684345531/100000000000000 : ℝ)^3695
        have hw : |(5181852407/10000000000 : ℝ)|=(5181852407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365112441/2500000000 : ℝ)|^4719 ≤ (46174924732371/100000000000000 : ℝ)^3695
        have hw : |(1365112441/2500000000 : ℝ)|=(1365112441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280008679/10000000000 : ℝ)*x 0 + (-1594977301/10000000000 : ℝ)*x 1 + (5460449691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280008679/10000000000 : ℝ)^4719 ≤ (11058800737371/25000000000000 : ℝ)^3695 := by
    have hnat : (5280008679 : ℕ)^4719*25000000000000^3695 ≤ 11058800737371^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280008679 10000000000 11058800737371 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1594977301/10000000000 : ℝ)^4719 ≤ (59936706819/625000000000 : ℝ)^3695 := by
    have hnat : (1594977301 : ℕ)^4719*625000000000^3695 ≤ 59936706819^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594977301 10000000000 59936706819 625000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460449691/10000000000 : ℝ)^4719 ≤ (4617492394399/10000000000000 : ℝ)^3695 := by
    have hnat : (5460449691 : ℕ)^4719*10000000000000^3695 ≤ 4617492394399^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460449691 10000000000 4617492394399 10000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280008679/10000000000 : ℝ), (-1594977301/10000000000 : ℝ), (5460449691/10000000000 : ℝ)] ![(11058800737371/25000000000000 : ℝ), (59936706819/625000000000 : ℝ), (4617492394399/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280008679/10000000000 : ℝ)|^4719 ≤ (11058800737371/25000000000000 : ℝ)^3695
        have hw : |(5280008679/10000000000 : ℝ)|=(5280008679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1594977301/10000000000 : ℝ)|^4719 ≤ (59936706819/625000000000 : ℝ)^3695
        have hw : |(-1594977301/10000000000 : ℝ)|=(1594977301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460449691/10000000000 : ℝ)|^4719 ≤ (4617492394399/10000000000000 : ℝ)^3695
        have hw : |(5460449691/10000000000 : ℝ)|=(5460449691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320002161/2500000000 : ℝ)*x 0 + (2730224863/5000000000 : ℝ)*x 1 + (-1594977301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320002161/2500000000 : ℝ)^4719 ≤ (11058800643749/25000000000000 : ℝ)^3695 := by
    have hnat : (1320002161 : ℕ)^4719*25000000000000^3695 ≤ 11058800643749^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320002161 2500000000 11058800643749 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730224863/5000000000 : ℝ)^4719 ≤ (46174924321981/100000000000000 : ℝ)^3695 := by
    have hnat : (2730224863 : ℕ)^4719*100000000000000^3695 ≤ 46174924321981^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730224863 5000000000 46174924321981 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594977301/10000000000 : ℝ)^4719 ≤ (59936706819/625000000000 : ℝ)^3695 := by
    have hnat : (1594977301 : ℕ)^4719*625000000000^3695 ≤ 59936706819^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594977301 10000000000 59936706819 625000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320002161/2500000000 : ℝ), (2730224863/5000000000 : ℝ), (-1594977301/10000000000 : ℝ)] ![(11058800643749/25000000000000 : ℝ), (46174924321981/100000000000000 : ℝ), (59936706819/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320002161/2500000000 : ℝ)|^4719 ≤ (11058800643749/25000000000000 : ℝ)^3695
        have hw : |(1320002161/2500000000 : ℝ)|=(1320002161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730224863/5000000000 : ℝ)|^4719 ≤ (46174924321981/100000000000000 : ℝ)^3695
        have hw : |(2730224863/5000000000 : ℝ)|=(2730224863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1594977301/10000000000 : ℝ)|^4719 ≤ (59936706819/625000000000 : ℝ)^3695
        have hw : |(-1594977301/10000000000 : ℝ)|=(1594977301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s4_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055259431/2500000000 : ℝ)*x 0 + (2284792281/5000000000 : ℝ)*x 1 + (3893981699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055259431/2500000000 : ℝ)^4719 ≤ (33236187038013/100000000000000 : ℝ)^3695 := by
    have hnat : (1055259431 : ℕ)^4719*100000000000000^3695 ≤ 33236187038013^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055259431 2500000000 33236187038013 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2284792281/5000000000 : ℝ)^4719 ≤ (36780525127271/100000000000000 : ℝ)^3695 := by
    have hnat : (2284792281 : ℕ)^4719*100000000000000^3695 ≤ 36780525127271^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284792281 5000000000 36780525127271 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3893981699/10000000000 : ℝ)^4719 ≤ (29983287825769/100000000000000 : ℝ)^3695 := by
    have hnat : (3893981699 : ℕ)^4719*100000000000000^3695 ≤ 29983287825769^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3893981699 10000000000 29983287825769 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055259431/2500000000 : ℝ), (2284792281/5000000000 : ℝ), (3893981699/10000000000 : ℝ)] ![(33236187038013/100000000000000 : ℝ), (36780525127271/100000000000000 : ℝ), (29983287825769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055259431/2500000000 : ℝ)|^4719 ≤ (33236187038013/100000000000000 : ℝ)^3695
        have hw : |(1055259431/2500000000 : ℝ)|=(1055259431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2284792281/5000000000 : ℝ)|^4719 ≤ (36780525127271/100000000000000 : ℝ)^3695
        have hw : |(2284792281/5000000000 : ℝ)|=(2284792281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3893981699/10000000000 : ℝ)|^4719 ≤ (29983287825769/100000000000000 : ℝ)^3695
        have hw : |(3893981699/10000000000 : ℝ)|=(3893981699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5183/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16359/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8187/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8187/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8187/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8187/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8187/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8187/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10353/100000 : ℝ) ^ (4715/1024 : ℝ) ≤ (729155382251731/25000000000000000000 : ℝ) := by
    have hpowers : (10353/100000 : ℝ)^4715 ≤ (729155382251731/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10353 : ℕ)^4715*25000000000000000000^1024 ≤ 729155382251731^1024*100000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10353 100000 729155382251731 25000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10353/100000 : ℝ)) (X := (729155382251731/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8187/50000 : ℝ) ^ (4715/1024 : ℝ) ≤ (6018965589587073/25000000000000000000 : ℝ) := by
    have hpowers : (8187/50000 : ℝ)^4715 ≤ (6018965589587073/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8187 : ℕ)^4715*25000000000000000000^1024 ≤ 6018965589587073^1024*50000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8187 50000 6018965589587073 25000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8187/50000 : ℝ)) (X := (6018965589587073/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500729155382251731/12500000000000000000 : ℝ) ≤ (50000633415113/50000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (12500729155382251731/12500000000000000000 : ℝ)^1024 ≤ (50000633415113/50000000000000 : ℝ)^4715 := by
      have hnat : (12500729155382251731 : ℕ)^1024*50000000000000^4715 ≤ 50000633415113^4715*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500729155382251731 12500000000000000000 50000633415113 50000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50000633415113/50000000000000 : ℝ)) (X := (12500729155382251731/12500000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251687030242959701/6250000000000000000 : ℝ) ≤ (2000117231744359/2000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (6251687030242959701/6250000000000000000 : ℝ)^1024 ≤ (2000117231744359/2000000000000000 : ℝ)^4715 := by
      have hnat : (6251687030242959701 : ℕ)^1024*2000000000000000^4715 ≤ 2000117231744359^4715*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251687030242959701 6250000000000000000 2000117231744359 2000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000117231744359/2000000000000000 : ℝ)) (X := (6251687030242959701/6250000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506018965589587073/12500000000000000000 : ℝ) ≤ (1000104563442099/1000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (12506018965589587073/12500000000000000000 : ℝ)^1024 ≤ (1000104563442099/1000000000000000 : ℝ)^4715 := by
      have hnat : (12506018965589587073 : ℕ)^1024*1000000000000000^4715 ≤ 1000104563442099^4715*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506018965589587073 12500000000000000000 1000104563442099 1000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000104563442099/1000000000000000 : ℝ)) (X := (12506018965589587073/12500000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(729155382251731/25000000000000000000 : ℝ) ≤ ((2006708295155051431/2007000000000000000 : ℝ)+2*(91895139839/120420000000000 : ℝ)*(10353/100000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (2006708295155051431/2007000000000000000 : ℝ)+2*(91895139839/120420000000000 : ℝ)*(10353/100000 : ℝ)=(50000633415113/50000000000000 : ℝ) by norm_num, show 1+2*(729155382251731/25000000000000000000 : ℝ)=(12500729155382251731/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6018965589587073/25000000000000000000 : ℝ)+(729155382251731/25000000000000000000 : ℝ) ≤ ((2006708295155051431/2007000000000000000 : ℝ)+(91895139839/120420000000000 : ℝ)*((8187/50000 : ℝ)+(10353/100000 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (2006708295155051431/2007000000000000000 : ℝ)+(91895139839/120420000000000 : ℝ)*((8187/50000 : ℝ)+(10353/100000 : ℝ))=(2000117231744359/2000000000000000 : ℝ) by norm_num, show 1+(6018965589587073/25000000000000000000 : ℝ)+(729155382251731/25000000000000000000 : ℝ)=(6251687030242959701/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6018965589587073/25000000000000000000 : ℝ) ≤ ((2006708295155051431/2007000000000000000 : ℝ)+2*(91895139839/120420000000000 : ℝ)*(8187/50000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (2006708295155051431/2007000000000000000 : ℝ)+2*(91895139839/120420000000000 : ℝ)*(8187/50000 : ℝ)=(1000104563442099/1000000000000000 : ℝ) by norm_num, show 1+2*(6018965589587073/25000000000000000000 : ℝ)=(12506018965589587073/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2006708295155051431/2007000000000000000 : ℝ)*(X 1 0+X 2 0)+(91895139839/120420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (10353/100000 : ℝ)) (hi := (8187/50000 : ℝ)) (c := (2006708295155051431/2007000000000000000 : ℝ)) (alpha := (91895139839/120420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2006708295155051431/2007000000000000000 : ℝ)*(X 0 1+X 2 1)+(91895139839/120420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (10353/100000 : ℝ)) (hi := (8187/50000 : ℝ)) (c := (2006708295155051431/2007000000000000000 : ℝ)) (alpha := (91895139839/120420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2006708295155051431/2007000000000000000 : ℝ)*(X 0 2+X 1 2)+(91895139839/120420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (10353/100000 : ℝ)) (hi := (8187/50000 : ℝ)) (c := (2006708295155051431/2007000000000000000 : ℝ)) (alpha := (91895139839/120420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-172977287/1000000000 : ℝ)*X 0 0+(2731282273/5000000000 : ℝ)*X 0 1+(647469949/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677486511/5000000000 : ℝ)*X 1 0+(-23445843/125000000 : ℝ)*X 1 1+(5179759591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677486511/5000000000 : ℝ)*X 2 0+(647469949/1250000000 : ℝ)*X 2 1+(-23445843/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((42208631/100000000 : ℝ)*X 0 0+(1944426647/5000000000 : ℝ)*X 0 1+(2287329849/5000000000 : ℝ)*X 0 2+(42208631/100000000 : ℝ)*X 1 0+(1944426647/5000000000 : ℝ)*X 1 1+(2287329849/5000000000 : ℝ)*X 1 2+(42208631/100000000 : ℝ)*X 2 0+(1944426647/5000000000 : ℝ)*X 2 1+(2287329849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86492243/500000000 : ℝ)*X 0 0+(5181852407/10000000000 : ℝ)*X 0 1+(1365112441/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280008679/10000000000 : ℝ)*X 1 0+(-1594977301/10000000000 : ℝ)*X 1 1+(5460449691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320002161/2500000000 : ℝ)*X 2 0+(2730224863/5000000000 : ℝ)*X 2 1+(-1594977301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1055259431/2500000000 : ℝ)*X 0 0+(2284792281/5000000000 : ℝ)*X 0 1+(3893981699/10000000000 : ℝ)*X 0 2+(1055259431/2500000000 : ℝ)*X 1 0+(2284792281/5000000000 : ℝ)*X 1 1+(3893981699/10000000000 : ℝ)*X 1 2+(1055259431/2500000000 : ℝ)*X 2 0+(2284792281/5000000000 : ℝ)*X 2 1+(3893981699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (153463689175664477904213197/12543750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2042053713/100000000000000 : ℝ)*(base19) + (955081701/50000000000000 : ℝ)*(base23) + (35313453/50000000000000 : ℝ)*(lower2) + (12144651/4000000000000 : ℝ)*(upper3) + (4143573/2000000000000 : ℝ)*(upper5) + (312138349625929/12500000000000 : ℝ)*(major0) + (312138349625929/12500000000000 : ℝ)*(major1) + (312138349625929/12500000000000 : ℝ)*(major2) + (1768015501124757/50000000000000 : ℝ)*(sp0) + (1768026599316343/50000000000000 : ℝ)*(sp1) + (3536053330522997/100000000000000 : ℝ)*(sp2) + (72907354673719/5000000000000 : ℝ)*(sp3) + (4847687377/20000000000000 : ℝ)*(sp4) + (2170408981/20000000000000 : ℝ)*(sp7) + (364539486379821/25000000000000 : ℝ)*(f.failure) + (3536055240686399/100000000000000 : ℝ)*(f.sum) + (2015286685823/1505250000000000000000000000 : ℝ)*base66 + (397922705966849303/75262500000000000000000000000000 : ℝ)*base68 + (161115804629024303/75262500000000000000000000000000 : ℝ)*base70 + (118254301720613197/75262500000000000000000000000000 : ℝ)*base71 + (7918912743421/3010500000000000000000000000 : ℝ)*base74 + (255089164078499303/75262500000000000000000000000000 : ℝ)*base76 + (323857163737088197/75262500000000000000000000000000 : ℝ)*base77 + (714806008117911803/75262500000000000000000000000000 : ℝ)*base80 + (1037877477193/6021000000000000000000000000 : ℝ)*base81 + (2876113/312500000000000000000 : ℝ)*base90 + (2876113/312500000000000000000 : ℝ)*base92 + (2876113/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4785991207917501732369541/557500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54489507/4000000000000 : ℝ)*(base19) + (1461663957/100000000000000 : ℝ)*(base23) + (6493377/1562500000000 : ℝ)*(lower1) + (176615941/100000000000000 : ℝ)*(upper3) + (28274237/50000000000000 : ℝ)*(lower4) + (181353471/100000000000000 : ℝ)*(upper5) + (253477358028067/10000000000000 : ℝ)*(major0) + (253477358028067/10000000000000 : ℝ)*(major1) + (253477358028067/10000000000000 : ℝ)*(major2) + (1135414517/100000000000000 : ℝ)*(sp2) + (717878765328213/20000000000000 : ℝ)*(sp4) + (358939246440339/10000000000000 : ℝ)*(sp5) + (3589391229562591/100000000000000 : ℝ)*(sp6) + (1480153047762347/100000000000000 : ℝ)*(sp7) + (1480153047762347/100000000000000 : ℝ)*(f.failure) + (717878765328213/20000000000000 : ℝ)*(f.sum) + (7382706997621/3010500000000000000000000000 : ℝ)*base65 + (540815537401701631/60210000000000000000000000000000 : ℝ)*base67 + (358375278955461631/60210000000000000000000000000000 : ℝ)*base69 + (1597427607152211631/60210000000000000000000000000000 : ℝ)*base71 + (10934993749513/3010500000000000000000000000 : ℝ)*base73 + (793616258548838369/60210000000000000000000000000000 : ℝ)*base76 + (490516420286931631/60210000000000000000000000000000 : ℝ)*base77 + (236315283129951631/60210000000000000000000000000000 : ℝ)*base79 + (4973937019423/1505250000000000000000000000 : ℝ)*base82 + (1583591/1250000000000000000000 : ℝ)*base90 + (1583591/1250000000000000000000 : ℝ)*base92 + (1583591/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1600_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8187/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1600_s5_0 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1729786413/10000000000 : ℝ)*x 0 + (2731249903/5000000000 : ℝ)*x 1 + (5179815299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1729786413/10000000000 : ℝ)^4719 ≤ (5318465952083/50000000000000 : ℝ)^3695 := by
    have hnat : (1729786413 : ℕ)^4719*50000000000000^3695 ≤ 5318465952083^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729786413 10000000000 5318465952083 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731249903/5000000000 : ℝ)^4719 ≤ (46197065805377/100000000000000 : ℝ)^3695 := by
    have hnat : (2731249903 : ℕ)^4719*100000000000000^3695 ≤ 46197065805377^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731249903 5000000000 46197065805377 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179815299/10000000000 : ℝ)^4719 ≤ (21583001136121/50000000000000 : ℝ)^3695 := by
    have hnat : (5179815299 : ℕ)^4719*50000000000000^3695 ≤ 21583001136121^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179815299 10000000000 21583001136121 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1729786413/10000000000 : ℝ), (2731249903/5000000000 : ℝ), (5179815299/10000000000 : ℝ)] ![(5318465952083/50000000000000 : ℝ), (46197065805377/100000000000000 : ℝ), (21583001136121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1729786413/10000000000 : ℝ)|^4719 ≤ (5318465952083/50000000000000 : ℝ)^3695
        have hw : |(-1729786413/10000000000 : ℝ)|=(1729786413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731249903/5000000000 : ℝ)|^4719 ≤ (46197065805377/100000000000000 : ℝ)^3695
        have hw : |(2731249903/5000000000 : ℝ)|=(2731249903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179815299/10000000000 : ℝ)|^4719 ≤ (21583001136121/50000000000000 : ℝ)^3695
        have hw : |(5179815299/10000000000 : ℝ)|=(5179815299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_1 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070991141/2000000000 : ℝ)*x 0 + (-375123427/2000000000 : ℝ)*x 1 + (5179815031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070991141/2000000000 : ℝ)^4719 ≤ (22519340289329/50000000000000 : ℝ)^3695 := by
    have hnat : (1070991141 : ℕ)^4719*50000000000000^3695 ≤ 22519340289329^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070991141 2000000000 22519340289329 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375123427/2000000000 : ℝ)^4719 ≤ (471812799169/4000000000000 : ℝ)^3695 := by
    have hnat : (375123427 : ℕ)^4719*4000000000000^3695 ≤ 471812799169^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375123427 2000000000 471812799169 4000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179815031/10000000000 : ℝ)^4719 ≤ (10791499854981/25000000000000 : ℝ)^3695 := by
    have hnat : (5179815031 : ℕ)^4719*25000000000000^3695 ≤ 10791499854981^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179815031 10000000000 10791499854981 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070991141/2000000000 : ℝ), (-375123427/2000000000 : ℝ), (5179815031/10000000000 : ℝ)] ![(22519340289329/50000000000000 : ℝ), (471812799169/4000000000000 : ℝ), (10791499854981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070991141/2000000000 : ℝ)|^4719 ≤ (22519340289329/50000000000000 : ℝ)^3695
        have hw : |(1070991141/2000000000 : ℝ)|=(1070991141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375123427/2000000000 : ℝ)|^4719 ≤ (471812799169/4000000000000 : ℝ)^3695
        have hw : |(-375123427/2000000000 : ℝ)|=(375123427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179815031/10000000000 : ℝ)|^4719 ≤ (10791499854981/25000000000000 : ℝ)^3695
        have hw : |(5179815031/10000000000 : ℝ)|=(5179815031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_2 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677477761/5000000000 : ℝ)*x 0 + (129495379/250000000 : ℝ)*x 1 + (-1875617211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677477761/5000000000 : ℝ)^4719 ≤ (45038678612961/100000000000000 : ℝ)^3695 := by
    have hnat : (2677477761 : ℕ)^4719*100000000000000^3695 ≤ 45038678612961^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677477761 5000000000 45038678612961 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129495379/250000000 : ℝ)^4719 ≤ (10791500198217/25000000000000 : ℝ)^3695 := by
    have hnat : (129495379 : ℕ)^4719*25000000000000^3695 ≤ 10791500198217^3695*250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129495379 250000000 10791500198217 25000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1875617211/10000000000 : ℝ)^4719 ≤ (94362564717/800000000000 : ℝ)^3695 := by
    have hnat : (1875617211 : ℕ)^4719*800000000000^3695 ≤ 94362564717^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875617211 10000000000 94362564717 800000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677477761/5000000000 : ℝ), (129495379/250000000 : ℝ), (-1875617211/10000000000 : ℝ)] ![(45038678612961/100000000000000 : ℝ), (10791500198217/25000000000000 : ℝ), (94362564717/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677477761/5000000000 : ℝ)|^4719 ≤ (45038678612961/100000000000000 : ℝ)^3695
        have hw : |(2677477761/5000000000 : ℝ)|=(2677477761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129495379/250000000 : ℝ)|^4719 ≤ (10791500198217/25000000000000 : ℝ)^3695
        have hw : |(129495379/250000000 : ℝ)|=(129495379/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1875617211/10000000000 : ℝ)|^4719 ≤ (94362564717/800000000000 : ℝ)^3695
        have hw : |(-1875617211/10000000000 : ℝ)|=(1875617211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_3 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (844174289/2000000000 : ℝ)*x 0 + (3888998057/10000000000 : ℝ)*x 1 + (571814143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844174289/2000000000 : ℝ)^4719 ≤ (1038578591779/3125000000000 : ℝ)^3695 := by
    have hnat : (844174289 : ℕ)^4719*3125000000000^3695 ≤ 1038578591779^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844174289 2000000000 1038578591779 3125000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3888998057/10000000000 : ℝ)^4719 ≤ (29934288436063/100000000000000 : ℝ)^3695 := by
    have hnat : (3888998057 : ℕ)^4719*100000000000000^3695 ≤ 29934288436063^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888998057 10000000000 29934288436063 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571814143/1250000000 : ℝ)^4719 ≤ (18415598304993/50000000000000 : ℝ)^3695 := by
    have hnat : (571814143 : ℕ)^4719*50000000000000^3695 ≤ 18415598304993^3695*1250000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571814143 1250000000 18415598304993 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844174289/2000000000 : ℝ), (3888998057/10000000000 : ℝ), (571814143/1250000000 : ℝ)] ![(1038578591779/3125000000000 : ℝ), (29934288436063/100000000000000 : ℝ), (18415598304993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844174289/2000000000 : ℝ)|^4719 ≤ (1038578591779/3125000000000 : ℝ)^3695
        have hw : |(844174289/2000000000 : ℝ)|=(844174289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3888998057/10000000000 : ℝ)|^4719 ≤ (29934288436063/100000000000000 : ℝ)^3695
        have hw : |(3888998057/10000000000 : ℝ)|=(3888998057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571814143/1250000000 : ℝ)|^4719 ≤ (18415598304993/50000000000000 : ℝ)^3695
        have hw : |(571814143/1250000000 : ℝ)|=(571814143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_4 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-864929199/5000000000 : ℝ)*x 0 + (5181906153/10000000000 : ℝ)*x 1 + (5460386947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864929199/5000000000 : ℝ)^4719 ≤ (664843577291/6250000000000 : ℝ)^3695 := by
    have hnat : (864929199 : ℕ)^4719*6250000000000^3695 ≤ 664843577291^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864929199 5000000000 664843577291 6250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181906153/10000000000 : ℝ)^4719 ≤ (21594128213043/50000000000000 : ℝ)^3695 := by
    have hnat : (5181906153 : ℕ)^4719*50000000000000^3695 ≤ 21594128213043^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181906153 10000000000 21594128213043 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460386947/10000000000 : ℝ)^4719 ≤ (23087123163081/50000000000000 : ℝ)^3695 := by
    have hnat : (5460386947 : ℕ)^4719*50000000000000^3695 ≤ 23087123163081^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460386947 10000000000 23087123163081 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-864929199/5000000000 : ℝ), (5181906153/10000000000 : ℝ), (5460386947/10000000000 : ℝ)] ![(664843577291/6250000000000 : ℝ), (21594128213043/50000000000000 : ℝ), (23087123163081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-864929199/5000000000 : ℝ)|^4719 ≤ (664843577291/6250000000000 : ℝ)^3695
        have hw : |(-864929199/5000000000 : ℝ)|=(864929199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181906153/10000000000 : ℝ)|^4719 ≤ (21594128213043/50000000000000 : ℝ)^3695
        have hw : |(5181906153/10000000000 : ℝ)|=(5181906153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460386947/10000000000 : ℝ)|^4719 ≤ (23087123163081/50000000000000 : ℝ)^3695
        have hw : |(5460386947/10000000000 : ℝ)|=(5460386947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_5 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640011633/5000000000 : ℝ)*x 0 + (-3115323/19531250 : ℝ)*x 1 + (1365096709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640011633/5000000000 : ℝ)^4719 ≤ (8847071805021/20000000000000 : ℝ)^3695 := by
    have hnat : (2640011633 : ℕ)^4719*20000000000000^3695 ≤ 8847071805021^3695*5000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640011633 5000000000 8847071805021 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3115323/19531250 : ℝ)^4719 ≤ (4795197914541/50000000000000 : ℝ)^3695 := by
    have hnat : (3115323 : ℕ)^4719*50000000000000^3695 ≤ 4795197914541^3695*19531250^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115323 19531250 4795197914541 50000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365096709/2500000000 : ℝ)^4719 ≤ (9234849025479/20000000000000 : ℝ)^3695 := by
    have hnat : (1365096709 : ℕ)^4719*20000000000000^3695 ≤ 9234849025479^3695*2500000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365096709 2500000000 9234849025479 20000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640011633/5000000000 : ℝ), (-3115323/19531250 : ℝ), (1365096709/2500000000 : ℝ)] ![(8847071805021/20000000000000 : ℝ), (4795197914541/50000000000000 : ℝ), (9234849025479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640011633/5000000000 : ℝ)|^4719 ≤ (8847071805021/20000000000000 : ℝ)^3695
        have hw : |(2640011633/5000000000 : ℝ)|=(2640011633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3115323/19531250 : ℝ)|^4719 ≤ (4795197914541/50000000000000 : ℝ)^3695
        have hw : |(-3115323/19531250 : ℝ)|=(3115323/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365096709/2500000000 : ℝ)|^4719 ≤ (9234849025479/20000000000000 : ℝ)^3695
        have hw : |(1365096709/2500000000 : ℝ)|=(1365096709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_6 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5280023211/10000000000 : ℝ)*x 0 + (5460386883/10000000000 : ℝ)*x 1 + (-1595045387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280023211/10000000000 : ℝ)^4719 ≤ (2764709902289/6250000000000 : ℝ)^3695 := by
    have hnat : (5280023211 : ℕ)^4719*6250000000000^3695 ≤ 2764709902289^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280023211 10000000000 2764709902289 6250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460386883/10000000000 : ℝ)^4719 ≤ (46174245634981/100000000000000 : ℝ)^3695 := by
    have hnat : (5460386883 : ℕ)^4719*100000000000000^3695 ≤ 46174245634981^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460386883 10000000000 46174245634981 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595045387/10000000000 : ℝ)^4719 ≤ (9590395913549/100000000000000 : ℝ)^3695 := by
    have hnat : (1595045387 : ℕ)^4719*100000000000000^3695 ≤ 9590395913549^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595045387 10000000000 9590395913549 100000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280023211/10000000000 : ℝ), (5460386883/10000000000 : ℝ), (-1595045387/10000000000 : ℝ)] ![(2764709902289/6250000000000 : ℝ), (46174245634981/100000000000000 : ℝ), (9590395913549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280023211/10000000000 : ℝ)|^4719 ≤ (2764709902289/6250000000000 : ℝ)^3695
        have hw : |(5280023211/10000000000 : ℝ)|=(5280023211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460386883/10000000000 : ℝ)|^4719 ≤ (46174245634981/100000000000000 : ℝ)^3695
        have hw : |(5460386883/10000000000 : ℝ)|=(5460386883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1595045387/10000000000 : ℝ)|^4719 ≤ (9590395913549/100000000000000 : ℝ)^3695
        have hw : |(-1595045387/10000000000 : ℝ)|=(1595045387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1600_s5_7 (p : ℝ) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4221045869/10000000000 : ℝ)*x 0 + (913888449/2000000000 : ℝ)*x 1 + (3894122137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221045869/10000000000 : ℝ)^4719 ≤ (519316702259/1562500000000 : ℝ)^3695 := by
    have hnat : (4221045869 : ℕ)^4719*1562500000000^3695 ≤ 519316702259^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221045869 10000000000 519316702259 1562500000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (913888449/2000000000 : ℝ)^4719 ≤ (1838953108499/5000000000000 : ℝ)^3695 := by
    have hnat : (913888449 : ℕ)^4719*5000000000000^3695 ≤ 1838953108499^3695*2000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913888449 2000000000 1838953108499 5000000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3894122137/10000000000 : ℝ)^4719 ≤ (374808360879/1250000000000 : ℝ)^3695 := by
    have hnat : (3894122137 : ℕ)^4719*1250000000000^3695 ≤ 374808360879^3695*10000000000^4719 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3894122137 10000000000 374808360879 1250000000000 4719 3695 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4719/1024 : ℝ)) 4719 3695 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221045869/10000000000 : ℝ), (913888449/2000000000 : ℝ), (3894122137/10000000000 : ℝ)] ![(519316702259/1562500000000 : ℝ), (1838953108499/5000000000000 : ℝ), (374808360879/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221045869/10000000000 : ℝ)|^4719 ≤ (519316702259/1562500000000 : ℝ)^3695
        have hw : |(4221045869/10000000000 : ℝ)|=(4221045869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(913888449/2000000000 : ℝ)|^4719 ≤ (1838953108499/5000000000000 : ℝ)^3695
        have hw : |(913888449/2000000000 : ℝ)|=(913888449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3894122137/10000000000 : ℝ)|^4719 ≤ (374808360879/1250000000000 : ℝ)^3695
        have hw : |(3894122137/10000000000 : ℝ)|=(3894122137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1600_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (324/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8179/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5183/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16359/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5183/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5183/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16359/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5183/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5183/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16359/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5183/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5183/50000 : ℝ) ^ (4715/1024 : ℝ) ≤ (1466761446181377/50000000000000000000 : ℝ) := by
    have hpowers : (5183/50000 : ℝ)^4715 ≤ (1466761446181377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5183 : ℕ)^4715*50000000000000000000^1024 ≤ 1466761446181377^1024*50000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5183 50000 1466761446181377 50000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5183/50000 : ℝ)) (X := (1466761446181377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16359/100000 : ℝ) ^ (4715/1024 : ℝ) ≤ (23974475184411791/100000000000000000000 : ℝ) := by
    have hpowers : (16359/100000 : ℝ)^4715 ≤ (23974475184411791/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16359 : ℕ)^4715*100000000000000000000^1024 ≤ 23974475184411791^1024*100000^4715 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16359 100000 23974475184411791 100000000000000000000 4715 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16359/100000 : ℝ)) (X := (23974475184411791/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001466761446181377/25000000000000000000 : ℝ) ≤ (2500031854278487/2500000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (25001466761446181377/25000000000000000000 : ℝ)^1024 ≤ (2500031854278487/2500000000000000 : ℝ)^4715 := by
      have hnat : (25001466761446181377 : ℕ)^1024*2500000000000000^4715 ≤ 2500031854278487^4715*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001466761446181377 25000000000000000000 2500031854278487 2500000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500031854278487/2500000000000000 : ℝ)) (X := (25001466761446181377/25000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005381599615354909/20000000000000000000 : ℝ) ≤ (10000584324252601/10000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (20005381599615354909/20000000000000000000 : ℝ)^1024 ≤ (10000584324252601/10000000000000000 : ℝ)^4715 := by
      have hnat : (20005381599615354909 : ℕ)^1024*10000000000000000^4715 ≤ 10000584324252601^4715*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005381599615354909 20000000000000000000 10000584324252601 10000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000584324252601/10000000000000000 : ℝ)) (X := (20005381599615354909/20000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023974475184411791/50000000000000000000 : ℝ) ≤ (5000520615695627/5000000000000000 : ℝ) ^ (4715/1024 : ℝ) := by
    have hpowers : (50023974475184411791/50000000000000000000 : ℝ)^1024 ≤ (5000520615695627/5000000000000000 : ℝ)^4715 := by
      have hnat : (50023974475184411791 : ℕ)^1024*5000000000000000^4715 ≤ 5000520615695627^4715*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023974475184411791 50000000000000000000 5000520615695627 5000000000000000 1024 4715 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000520615695627/5000000000000000 : ℝ)) (X := (50023974475184411791/50000000000000000000 : ℝ)) (by norm_num) 4715 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1466761446181377/50000000000000000000 : ℝ) ≤ ((3745080688247833523/3745625000000000000 : ℝ)+2*(456907138653/599300000000000 : ℝ)*(5183/50000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (3745080688247833523/3745625000000000000 : ℝ)+2*(456907138653/599300000000000 : ℝ)*(5183/50000 : ℝ)=(2500031854278487/2500000000000000 : ℝ) by norm_num, show 1+2*(1466761446181377/50000000000000000000 : ℝ)=(25001466761446181377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23974475184411791/100000000000000000000 : ℝ)+(1466761446181377/50000000000000000000 : ℝ) ≤ ((3745080688247833523/3745625000000000000 : ℝ)+(456907138653/599300000000000 : ℝ)*((16359/100000 : ℝ)+(5183/50000 : ℝ)))^(4715/1024 : ℝ) := by
    rw [show (3745080688247833523/3745625000000000000 : ℝ)+(456907138653/599300000000000 : ℝ)*((16359/100000 : ℝ)+(5183/50000 : ℝ))=(10000584324252601/10000000000000000 : ℝ) by norm_num, show 1+(23974475184411791/100000000000000000000 : ℝ)+(1466761446181377/50000000000000000000 : ℝ)=(20005381599615354909/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23974475184411791/100000000000000000000 : ℝ) ≤ ((3745080688247833523/3745625000000000000 : ℝ)+2*(456907138653/599300000000000 : ℝ)*(16359/100000 : ℝ))^(4715/1024 : ℝ) := by
    rw [show (3745080688247833523/3745625000000000000 : ℝ)+2*(456907138653/599300000000000 : ℝ)*(16359/100000 : ℝ)=(5000520615695627/5000000000000000 : ℝ) by norm_num, show 1+2*(23974475184411791/100000000000000000000 : ℝ)=(50023974475184411791/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3745080688247833523/3745625000000000000 : ℝ)*(X 1 0+X 2 0)+(456907138653/599300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (5183/50000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (3745080688247833523/3745625000000000000 : ℝ)) (alpha := (456907138653/599300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3745080688247833523/3745625000000000000 : ℝ)*(X 0 1+X 2 1)+(456907138653/599300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (5183/50000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (3745080688247833523/3745625000000000000 : ℝ)) (alpha := (456907138653/599300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3745080688247833523/3745625000000000000 : ℝ)*(X 0 2+X 1 2)+(456907138653/599300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4715/1024 : ℝ)) (lo := (5183/50000 : ℝ)) (hi := (16359/100000 : ℝ)) (c := (3745080688247833523/3745625000000000000 : ℝ)) (alpha := (456907138653/599300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1729786413/10000000000 : ℝ)*X 0 0+(2731249903/5000000000 : ℝ)*X 0 1+(5179815299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070991141/2000000000 : ℝ)*X 1 0+(-375123427/2000000000 : ℝ)*X 1 1+(5179815031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677477761/5000000000 : ℝ)*X 2 0+(129495379/250000000 : ℝ)*X 2 1+(-1875617211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((844174289/2000000000 : ℝ)*X 0 0+(3888998057/10000000000 : ℝ)*X 0 1+(571814143/1250000000 : ℝ)*X 0 2+(844174289/2000000000 : ℝ)*X 1 0+(3888998057/10000000000 : ℝ)*X 1 1+(571814143/1250000000 : ℝ)*X 1 2+(844174289/2000000000 : ℝ)*X 2 0+(3888998057/10000000000 : ℝ)*X 2 1+(571814143/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-864929199/5000000000 : ℝ)*X 0 0+(5181906153/10000000000 : ℝ)*X 0 1+(5460386947/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640011633/5000000000 : ℝ)*X 1 0+(-3115323/19531250 : ℝ)*X 1 1+(1365096709/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280023211/10000000000 : ℝ)*X 2 0+(5460386883/10000000000 : ℝ)*X 2 1+(-1595045387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4221045869/10000000000 : ℝ)*X 0 0+(913888449/2000000000 : ℝ)*X 0 1+(3894122137/10000000000 : ℝ)*X 0 2+(4221045869/10000000000 : ℝ)*X 1 0+(913888449/2000000000 : ℝ)*X 1 1+(3894122137/10000000000 : ℝ)*X 1 2+(4221045869/10000000000 : ℝ)*X 2 0+(913888449/2000000000 : ℝ)*X 2 1+(3894122137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1600_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (908904765507689009483481/234101562500000000000000000000 : ℝ) := by norm_num
    linear_combination (696047569/100000000000000 : ℝ)*(base19) + (494691071/100000000000000 : ℝ)*(base23) + (46035259/100000000000000 : ℝ)*(lower2) + (33359497/25000000000000 : ℝ)*(upper3) + (368301/12500000000000 : ℝ)*(lower4) + (24981431595217/1000000000000 : ℝ)*(major0) + (24981431595217/1000000000000 : ℝ)*(major1) + (24981431595217/1000000000000 : ℝ)*(major2) + (707503849719813/20000000000000 : ℝ)*(sp0) + (1768761187805277/50000000000000 : ℝ)*(sp1) + (3537522576967053/100000000000000 : ℝ)*(sp2) + (1458759580738201/100000000000000 : ℝ)*(sp3) + (3823059059/100000000000000 : ℝ)*(sp4) + (3537229627/100000000000000 : ℝ)*(sp7) + (364690779491957/25000000000000 : ℝ)*(f.failure) + (884380767914531/25000000000000 : ℝ)*(f.sum) + (19177045532113/5993000000000000000000000000 : ℝ)*base66 + (1197291251261221/936406250000000000000000000000 : ℝ)*base68 + (10649800781386817/1872812500000000000000000000000 : ℝ)*base70 + (34086703578343009/3745625000000000000000000000000 : ℝ)*base72 + (98982730503/2996500000000000000000000000 : ℝ)*base74 + (12622599964941279/936406250000000000000000000000 : ℝ)*base75 + (2151153099173009/3745625000000000000000000000000 : ℝ)*base78 + (824957298980741/3745625000000000000000000000000 : ℝ)*base79 + (310411204559/149825000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2751079/312500000000000000000 : ℝ)*base89 + (2751079/312500000000000000000 : ℝ)*base91 + (2751079/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1147256887940759475407329293/93640625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (993698977/50000000000000 : ℝ)*(base19) + (422598631/20000000000000 : ℝ)*(base23) + (305696887/50000000000000 : ℝ)*(lower1) + (250949151/100000000000000 : ℝ)*(upper3) + (76766741/100000000000000 : ℝ)*(lower4) + (132881541/50000000000000 : ℝ)*(upper5) + (1267914797067001/50000000000000 : ℝ)*(major0) + (1267914797067001/50000000000000 : ℝ)*(major1) + (1267914797067001/50000000000000 : ℝ)*(major2) + (1240812583/100000000000000 : ℝ)*(sp2) + (1795444542242299/50000000000000 : ℝ)*(sp4) + (897721774271661/25000000000000 : ℝ)*(sp5) + (179544286533943/5000000000000 : ℝ)*(sp6) + (1480769695393381/100000000000000 : ℝ)*(sp7) + (1480769695393381/100000000000000 : ℝ)*(f.failure) + (1795444542242299/50000000000000 : ℝ)*(f.sum) + (74580784597281/29965000000000000000000000000 : ℝ)*base65 + (794032733762487023/187281250000000000000000000000000 : ℝ)*base67 + (275243882376487023/187281250000000000000000000000000 : ℝ)*base69 + (729900038758674523/187281250000000000000000000000000 : ℝ)*base71 + (123283597473659/29965000000000000000000000000 : ℝ)*base74 + (4824815584393549523/187281250000000000000000000000000 : ℝ)*base75 + (1188347031332862023/187281250000000000000000000000000 : ℝ)*base77 + (651395557048799523/187281250000000000000000000000000 : ℝ)*base79 + (108126026238977/14982500000000000000000000000 : ℝ)*base82 + (9810793/1250000000000000000000 : ℝ)*base90 + (9810793/1250000000000000000000 : ℝ)*base92 + (9810793/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1600_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5183/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1600_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1600_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1600_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1600_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1600_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4715/1024 : ℝ) ≤ p) (hpb : p ≤ (4719/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21406347/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8269/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5103/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (324/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1600_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
