-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1155_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:37:47.422022+00:00
-- url     : https://prove2.me/submissions/27063995-f54d-46cf-a26a-db1694a0c562

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
theorem support_rectangle_w1155_s6_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080328701/5000000000 : ℝ)*x 0 + (5393121163/10000000000 : ℝ)*x 1 + (658205313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080328701/5000000000 : ℝ)^2087 ≤ (13130265862629/100000000000000 : ℝ)^1575 := by
    have hnat : (1080328701 : ℕ)^2087*100000000000000^1575 ≤ 13130265862629^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080328701 5000000000 13130265862629 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393121163/10000000000 : ℝ)^2087 ≤ (44123194990229/100000000000000 : ℝ)^1575 := by
    have hnat : (5393121163 : ℕ)^2087*100000000000000^1575 ≤ 44123194990229^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393121163 10000000000 44123194990229 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658205313/1250000000 : ℝ)^2087 ≤ (5343317392249/12500000000000 : ℝ)^1575 := by
    have hnat : (658205313 : ℕ)^2087*12500000000000^1575 ≤ 5343317392249^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658205313 1250000000 5343317392249 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080328701/5000000000 : ℝ), (5393121163/10000000000 : ℝ), (658205313/1250000000 : ℝ)] ![(13130265862629/100000000000000 : ℝ), (44123194990229/100000000000000 : ℝ), (5343317392249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080328701/5000000000 : ℝ)|^2087 ≤ (13130265862629/100000000000000 : ℝ)^1575
        have hw : |(-1080328701/5000000000 : ℝ)|=(1080328701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393121163/10000000000 : ℝ)|^2087 ≤ (44123194990229/100000000000000 : ℝ)^1575
        have hw : |(5393121163/10000000000 : ℝ)|=(5393121163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658205313/1250000000 : ℝ)|^2087 ≤ (5343317392249/12500000000000 : ℝ)^1575
        have hw : |(658205313/1250000000 : ℝ)|=(658205313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672394929/5000000000 : ℝ)*x 0 + (-2225318031/10000000000 : ℝ)*x 1 + (658205313/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672394929/5000000000 : ℝ)^2087 ≤ (2725000055453/6250000000000 : ℝ)^1575 := by
    have hnat : (2672394929 : ℕ)^2087*6250000000000^1575 ≤ 2725000055453^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672394929 5000000000 2725000055453 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225318031/10000000000 : ℝ)^2087 ≤ (13653459953309/100000000000000 : ℝ)^1575 := by
    have hnat : (2225318031 : ℕ)^2087*100000000000000^1575 ≤ 13653459953309^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225318031 10000000000 13653459953309 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658205313/1250000000 : ℝ)^2087 ≤ (5343317392249/12500000000000 : ℝ)^1575 := by
    have hnat : (658205313 : ℕ)^2087*12500000000000^1575 ≤ 5343317392249^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658205313 1250000000 5343317392249 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672394929/5000000000 : ℝ), (-2225318031/10000000000 : ℝ), (658205313/1250000000 : ℝ)] ![(2725000055453/6250000000000 : ℝ), (13653459953309/100000000000000 : ℝ), (5343317392249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672394929/5000000000 : ℝ)|^2087 ≤ (2725000055453/6250000000000 : ℝ)^1575
        have hw : |(2672394929/5000000000 : ℝ)|=(2672394929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225318031/10000000000 : ℝ)|^2087 ≤ (13653459953309/100000000000000 : ℝ)^1575
        have hw : |(-2225318031/10000000000 : ℝ)|=(2225318031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658205313/1250000000 : ℝ)|^2087 ≤ (5343317392249/12500000000000 : ℝ)^1575
        have hw : |(658205313/1250000000 : ℝ)|=(658205313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344789857/10000000000 : ℝ)*x 0 + (5265642503/10000000000 : ℝ)*x 1 + (-1112659017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344789857/10000000000 : ℝ)^2087 ≤ (43600000876439/100000000000000 : ℝ)^1575 := by
    have hnat : (5344789857 : ℕ)^2087*100000000000000^1575 ≤ 43600000876439^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344789857 10000000000 43600000876439 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265642503/10000000000 : ℝ)^2087 ≤ (8549307825447/20000000000000 : ℝ)^1575 := by
    have hnat : (5265642503 : ℕ)^2087*20000000000000^1575 ≤ 8549307825447^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265642503 10000000000 8549307825447 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112659017/5000000000 : ℝ)^2087 ≤ (13653459977699/100000000000000 : ℝ)^1575 := by
    have hnat : (1112659017 : ℕ)^2087*100000000000000^1575 ≤ 13653459977699^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112659017 5000000000 13653459977699 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344789857/10000000000 : ℝ), (5265642503/10000000000 : ℝ), (-1112659017/5000000000 : ℝ)] ![(43600000876439/100000000000000 : ℝ), (8549307825447/20000000000000 : ℝ), (13653459977699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344789857/10000000000 : ℝ)|^2087 ≤ (43600000876439/100000000000000 : ℝ)^1575
        have hw : |(5344789857/10000000000 : ℝ)|=(5344789857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265642503/10000000000 : ℝ)|^2087 ≤ (8549307825447/20000000000000 : ℝ)^1575
        have hw : |(5265642503/10000000000 : ℝ)|=(5265642503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112659017/5000000000 : ℝ)|^2087 ≤ (13653459977699/100000000000000 : ℝ)^1575
        have hw : |(-1112659017/5000000000 : ℝ)|=(1112659017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1090707241/2500000000 : ℝ)*x 0 + (423753537/1000000000 : ℝ)*x 1 + (4491797721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090707241/2500000000 : ℝ)^2087 ≤ (16658437477567/50000000000000 : ℝ)^1575 := by
    have hnat : (1090707241 : ℕ)^2087*50000000000000^1575 ≤ 16658437477567^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090707241 2500000000 16658437477567 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423753537/1000000000 : ℝ)^2087 ≤ (32054984874881/100000000000000 : ℝ)^1575 := by
    have hnat : (423753537 : ℕ)^2087*100000000000000^1575 ≤ 32054984874881^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423753537 1000000000 32054984874881 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491797721/10000000000 : ℝ)^2087 ≤ (1731407007881/5000000000000 : ℝ)^1575 := by
    have hnat : (4491797721 : ℕ)^2087*5000000000000^1575 ≤ 1731407007881^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491797721 10000000000 1731407007881 5000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090707241/2500000000 : ℝ), (423753537/1000000000 : ℝ), (4491797721/10000000000 : ℝ)] ![(16658437477567/50000000000000 : ℝ), (32054984874881/100000000000000 : ℝ), (1731407007881/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090707241/2500000000 : ℝ)|^2087 ≤ (16658437477567/50000000000000 : ℝ)^1575
        have hw : |(1090707241/2500000000 : ℝ)|=(1090707241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423753537/1000000000 : ℝ)|^2087 ≤ (32054984874881/100000000000000 : ℝ)^1575
        have hw : |(423753537/1000000000 : ℝ)|=(423753537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491797721/10000000000 : ℝ)|^2087 ≤ (1731407007881/5000000000000 : ℝ)^1575
        have hw : |(4491797721/10000000000 : ℝ)|=(4491797721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160662707/10000000000 : ℝ)*x 0 + (1316490907/2500000000 : ℝ)*x 1 + (5392798579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160662707/10000000000 : ℝ)^2087 ≤ (6565154290519/50000000000000 : ℝ)^1575 := by
    have hnat : (2160662707 : ℕ)^2087*50000000000000^1575 ≤ 6565154290519^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160662707 10000000000 6565154290519 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316490907/2500000000 : ℝ)^2087 ≤ (10687498376393/25000000000000 : ℝ)^1575 := by
    have hnat : (1316490907 : ℕ)^2087*25000000000000^1575 ≤ 10687498376393^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316490907 2500000000 10687498376393 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392798579/10000000000 : ℝ)^2087 ≤ (11029924474137/25000000000000 : ℝ)^1575 := by
    have hnat : (5392798579 : ℕ)^2087*25000000000000^1575 ≤ 11029924474137^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392798579 10000000000 11029924474137 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160662707/10000000000 : ℝ), (1316490907/2500000000 : ℝ), (5392798579/10000000000 : ℝ)] ![(6565154290519/50000000000000 : ℝ), (10687498376393/25000000000000 : ℝ), (11029924474137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160662707/10000000000 : ℝ)|^2087 ≤ (6565154290519/50000000000000 : ℝ)^1575
        have hw : |(-2160662707/10000000000 : ℝ)|=(2160662707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316490907/2500000000 : ℝ)|^2087 ≤ (10687498376393/25000000000000 : ℝ)^1575
        have hw : |(1316490907/2500000000 : ℝ)|=(1316490907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392798579/10000000000 : ℝ)|^2087 ≤ (11029924474137/25000000000000 : ℝ)^1575
        have hw : |(5392798579/10000000000 : ℝ)|=(5392798579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312461731/10000000000 : ℝ)*x 0 + (-2098162653/10000000000 : ℝ)*x 1 + (67409973/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312461731/10000000000 : ℝ)^2087 ≤ (43250900332817/100000000000000 : ℝ)^1575 := by
    have hnat : (5312461731 : ℕ)^2087*100000000000000^1575 ≤ 43250900332817^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312461731 10000000000 43250900332817 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098162653/10000000000 : ℝ)^2087 ≤ (20207055639/160000000000 : ℝ)^1575 := by
    have hnat : (2098162653 : ℕ)^2087*160000000000^1575 ≤ 20207055639^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098162653 10000000000 20207055639 160000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67409973/125000000 : ℝ)^2087 ≤ (44119689885217/100000000000000 : ℝ)^1575 := by
    have hnat : (67409973 : ℕ)^2087*100000000000000^1575 ≤ 44119689885217^1575*125000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67409973 125000000 44119689885217 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312461731/10000000000 : ℝ), (-2098162653/10000000000 : ℝ), (67409973/125000000 : ℝ)] ![(43250900332817/100000000000000 : ℝ), (20207055639/160000000000 : ℝ), (44119689885217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312461731/10000000000 : ℝ)|^2087 ≤ (43250900332817/100000000000000 : ℝ)^1575
        have hw : |(5312461731/10000000000 : ℝ)|=(5312461731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098162653/10000000000 : ℝ)|^2087 ≤ (20207055639/160000000000 : ℝ)^1575
        have hw : |(-2098162653/10000000000 : ℝ)|=(2098162653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67409973/125000000 : ℝ)|^2087 ≤ (44119689885217/100000000000000 : ℝ)^1575
        have hw : |(67409973/125000000 : ℝ)|=(67409973/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531246151/1000000000 : ℝ)*x 0 + (2696399221/5000000000 : ℝ)*x 1 + (-2098162133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531246151/1000000000 : ℝ)^2087 ≤ (43250897948667/100000000000000 : ℝ)^1575 := by
    have hnat : (531246151 : ℕ)^2087*100000000000000^1575 ≤ 43250897948667^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531246151 1000000000 43250897948667 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696399221/5000000000 : ℝ)^2087 ≤ (22059848205681/50000000000000 : ℝ)^1575 := by
    have hnat : (2696399221 : ℕ)^2087*50000000000000^1575 ≤ 22059848205681^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696399221 5000000000 22059848205681 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098162133/10000000000 : ℝ)^2087 ≤ (12629405626849/100000000000000 : ℝ)^1575 := by
    have hnat : (2098162133 : ℕ)^2087*100000000000000^1575 ≤ 12629405626849^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098162133 10000000000 12629405626849 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531246151/1000000000 : ℝ), (2696399221/5000000000 : ℝ), (-2098162133/10000000000 : ℝ)] ![(43250897948667/100000000000000 : ℝ), (22059848205681/50000000000000 : ℝ), (12629405626849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531246151/1000000000 : ℝ)|^2087 ≤ (43250897948667/100000000000000 : ℝ)^1575
        have hw : |(531246151/1000000000 : ℝ)|=(531246151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696399221/5000000000 : ℝ)|^2087 ≤ (22059848205681/50000000000000 : ℝ)^1575
        have hw : |(2696399221/5000000000 : ℝ)|=(2696399221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098162133/10000000000 : ℝ)|^2087 ≤ (12629405626849/100000000000000 : ℝ)^1575
        have hw : |(-2098162133/10000000000 : ℝ)|=(2098162133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s6_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (872567761/2000000000 : ℝ)*x 0 + (1122788669/2500000000 : ℝ)*x 1 + (4238180747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872567761/2000000000 : ℝ)^2087 ≤ (16658487268167/50000000000000 : ℝ)^1575 := by
    have hnat : (872567761 : ℕ)^2087*50000000000000^1575 ≤ 16658487268167^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872567761 2000000000 16658487268167 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122788669/2500000000 : ℝ)^2087 ≤ (6924314283359/20000000000000 : ℝ)^1575 := by
    have hnat : (1122788669 : ℕ)^2087*20000000000000^1575 ≤ 6924314283359^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122788669 2500000000 6924314283359 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238180747/10000000000 : ℝ)^2087 ≤ (32061454041923/100000000000000 : ℝ)^1575 := by
    have hnat : (4238180747 : ℕ)^2087*100000000000000^1575 ≤ 32061454041923^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238180747 10000000000 32061454041923 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872567761/2000000000 : ℝ), (1122788669/2500000000 : ℝ), (4238180747/10000000000 : ℝ)] ![(16658487268167/50000000000000 : ℝ), (6924314283359/20000000000000 : ℝ), (32061454041923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872567761/2000000000 : ℝ)|^2087 ≤ (16658487268167/50000000000000 : ℝ)^1575
        have hw : |(872567761/2000000000 : ℝ)|=(872567761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122788669/2500000000 : ℝ)|^2087 ≤ (6924314283359/20000000000000 : ℝ)^1575
        have hw : |(1122788669/2500000000 : ℝ)|=(1122788669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238180747/10000000000 : ℝ)|^2087 ≤ (32061454041923/100000000000000 : ℝ)^1575
        have hw : |(4238180747/10000000000 : ℝ)|=(4238180747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (879/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5667/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7047/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5667/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7047/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5667/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5667/50000 : ℝ) ^ (8347/2048 : ℝ) ≤ (1399475036775967/10000000000000000000 : ℝ) := by
    have hpowers : (5667/50000 : ℝ)^8347 ≤ (1399475036775967/10000000000000000000 : ℝ)^2048 := by
      have hnat : (5667 : ℕ)^8347*10000000000000000000^2048 ≤ 1399475036775967^2048*50000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5667 50000 1399475036775967 10000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5667/50000 : ℝ)) (X := (1399475036775967/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7047/50000 : ℝ) ^ (8347/2048 : ℝ) ≤ (34019891472339373/100000000000000000000 : ℝ) := by
    have hpowers : (7047/50000 : ℝ)^8347 ≤ (34019891472339373/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7047 : ℕ)^8347*100000000000000000000^2048 ≤ 34019891472339373^2048*50000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7047 50000 34019891472339373 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7047/50000 : ℝ)) (X := (34019891472339373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001399475036775967/5000000000000000000 : ℝ) ≤ (10000686671195041/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (5001399475036775967/5000000000000000000 : ℝ)^2048 ≤ (10000686671195041/10000000000000000 : ℝ)^8347 := by
      have hnat : (5001399475036775967 : ℕ)^2048*10000000000000000^8347 ≤ 10000686671195041^8347*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001399475036775967 5000000000000000000 10000686671195041 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000686671195041/10000000000000000 : ℝ)) (X := (5001399475036775967/5000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048014641840099043/100000000000000000000 : ℝ) ≤ (10001177862422171/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (100048014641840099043/100000000000000000000 : ℝ)^2048 ≤ (10001177862422171/10000000000000000 : ℝ)^8347 := by
      have hnat : (100048014641840099043 : ℕ)^2048*10000000000000000^8347 ≤ 10001177862422171^8347*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048014641840099043 100000000000000000000 10001177862422171 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001177862422171/10000000000000000 : ℝ)) (X := (100048014641840099043/100000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034019891472339373/50000000000000000000 : ℝ) ≤ (10001669053649301/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50034019891472339373/50000000000000000000 : ℝ)^2048 ≤ (10001669053649301/10000000000000000 : ℝ)^8347 := by
      have hnat : (50034019891472339373 : ℕ)^2048*10000000000000000^8347 ≤ 10001669053649301^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034019891472339373 50000000000000000000 10001669053649301 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001669053649301/10000000000000000 : ℝ)) (X := (50034019891472339373/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1399475036775967/10000000000000000000 : ℝ) ≤ ((4998326248145241/5000000000000000 : ℝ)+2*(2135614031/1200000000000 : ℝ)*(5667/50000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (4998326248145241/5000000000000000 : ℝ)+2*(2135614031/1200000000000 : ℝ)*(5667/50000 : ℝ)=(10000686671195041/10000000000000000 : ℝ) by norm_num, show 1+2*(1399475036775967/10000000000000000000 : ℝ)=(5001399475036775967/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34019891472339373/100000000000000000000 : ℝ)+(1399475036775967/10000000000000000000 : ℝ) ≤ ((4998326248145241/5000000000000000 : ℝ)+(2135614031/1200000000000 : ℝ)*((7047/50000 : ℝ)+(5667/50000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (4998326248145241/5000000000000000 : ℝ)+(2135614031/1200000000000 : ℝ)*((7047/50000 : ℝ)+(5667/50000 : ℝ))=(10001177862422171/10000000000000000 : ℝ) by norm_num, show 1+(34019891472339373/100000000000000000000 : ℝ)+(1399475036775967/10000000000000000000 : ℝ)=(100048014641840099043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34019891472339373/100000000000000000000 : ℝ) ≤ ((4998326248145241/5000000000000000 : ℝ)+2*(2135614031/1200000000000 : ℝ)*(7047/50000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (4998326248145241/5000000000000000 : ℝ)+2*(2135614031/1200000000000 : ℝ)*(7047/50000 : ℝ)=(10001669053649301/10000000000000000 : ℝ) by norm_num, show 1+2*(34019891472339373/100000000000000000000 : ℝ)=(50034019891472339373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4998326248145241/5000000000000000 : ℝ)*(X 1 0+X 2 0)+(2135614031/1200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (4998326248145241/5000000000000000 : ℝ)) (alpha := (2135614031/1200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4998326248145241/5000000000000000 : ℝ)*(X 0 1+X 2 1)+(2135614031/1200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (4998326248145241/5000000000000000 : ℝ)) (alpha := (2135614031/1200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4998326248145241/5000000000000000 : ℝ)*(X 0 2+X 1 2)+(2135614031/1200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (5667/50000 : ℝ)) (hi := (7047/50000 : ℝ)) (c := (4998326248145241/5000000000000000 : ℝ)) (alpha := (2135614031/1200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080328701/5000000000 : ℝ)*X 0 0+(5393121163/10000000000 : ℝ)*X 0 1+(658205313/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672394929/5000000000 : ℝ)*X 1 0+(-2225318031/10000000000 : ℝ)*X 1 1+(658205313/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344789857/10000000000 : ℝ)*X 2 0+(5265642503/10000000000 : ℝ)*X 2 1+(-1112659017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090707241/2500000000 : ℝ)*X 0 0+(423753537/1000000000 : ℝ)*X 0 1+(4491797721/10000000000 : ℝ)*X 0 2+(1090707241/2500000000 : ℝ)*X 1 0+(423753537/1000000000 : ℝ)*X 1 1+(4491797721/10000000000 : ℝ)*X 1 2+(1090707241/2500000000 : ℝ)*X 2 0+(423753537/1000000000 : ℝ)*X 2 1+(4491797721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2160662707/10000000000 : ℝ)*X 0 0+(1316490907/2500000000 : ℝ)*X 0 1+(5392798579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312461731/10000000000 : ℝ)*X 1 0+(-2098162653/10000000000 : ℝ)*X 1 1+(67409973/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531246151/1000000000 : ℝ)*X 2 0+(2696399221/5000000000 : ℝ)*X 2 1+(-2098162133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872567761/2000000000 : ℝ)*X 0 0+(1122788669/2500000000 : ℝ)*X 0 1+(4238180747/10000000000 : ℝ)*X 0 2+(872567761/2000000000 : ℝ)*X 1 0+(1122788669/2500000000 : ℝ)*X 1 1+(4238180747/10000000000 : ℝ)*X 1 2+(872567761/2000000000 : ℝ)*X 2 0+(1122788669/2500000000 : ℝ)*X 2 1+(4238180747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (302858528726866089641999/31250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23837837/1250000000000 : ℝ)*(base19) + (110899851/6250000000000 : ℝ)*(base23) + (70103141/100000000000000 : ℝ)*(lower2) + (240399/97656250000 : ℝ)*(upper3) + (14431533/10000000000000 : ℝ)*(upper5) + (1472194451178787/25000000000000 : ℝ)*(major0) + (1472194451178787/25000000000000 : ℝ)*(major1) + (1472194451178787/25000000000000 : ℝ)*(major2) + (3922252324017119/50000000000000 : ℝ)*(sp0) + (7844554385111813/100000000000000 : ℝ)*(sp1) + (7844554517741157/100000000000000 : ℝ)*(sp2) + (983242715047033/25000000000000 : ℝ)*(sp3) + (10328820907/20000000000000 : ℝ)*(sp4) + (28134054283/100000000000000 : ℝ)*(sp7) + (245812437140151/6250000000000 : ℝ)*(f.failure) + (7844556292138773/100000000000000 : ℝ)*(f.sum) + (36617243267/15000000000000000000000000 : ℝ)*base65 + (2174612286820501/375000000000000000000000000000 : ℝ)*base67 + (3124447398820501/375000000000000000000000000000 : ℝ)*base69 + (1961926651195501/375000000000000000000000000000 : ℝ)*base71 + (30622085611/7500000000000000000000000 : ℝ)*base73 + (5528275385695501/375000000000000000000000000000 : ℝ)*base75 + (1100567846929499/375000000000000000000000000000 : ℝ)*base78 + (14697600712945501/375000000000000000000000000000 : ℝ)*base79 + (516618623/234375000000000000000000 : ℝ)*base81 + (1219967/625000000000000000000 : ℝ)*base89 + (1219967/625000000000000000000 : ℝ)*base91 + (1219967/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3204072723188981453/400000000000000000000000 : ℝ) := by norm_num
    linear_combination (2207503449/100000000000000 : ℝ)*(base19) + (2429773059/100000000000000 : ℝ)*(base23) + (3664563/1562500000000 : ℝ)*(upper2) + (635567147/100000000000000 : ℝ)*(upper5) + (591866558415241/10000000000000 : ℝ)*(major0) + (591866558415241/10000000000000 : ℝ)*(major1) + (591866558415241/10000000000000 : ℝ)*(major2) + (2674081963/6250000000000 : ℝ)*(sp0) + (15389487343/20000000000000 : ℝ)*(sp1) + (94823602069/100000000000000 : ℝ)*(sp2) + (3942163830543943/50000000000000 : ℝ)*(sp4) + (7884291291459131/100000000000000 : ℝ)*(sp5) + (7884273193024167/100000000000000 : ℝ)*(sp6) + (3952960454899459/100000000000000 : ℝ)*(sp7) + (3952960454899459/100000000000000 : ℝ)*(f.failure) + (1576874089279859/20000000000000 : ℝ)*(f.sum) + (2611064009/6000000000000000000000000 : ℝ)*base65 + (598449019541743/150000000000000000000000000000 : ℝ)*base67 + (761340424091743/150000000000000000000000000000 : ℝ)*base69 + (1051716059958257/150000000000000000000000000000 : ℝ)*base72 + (3723363797/1200000000000000000000000 : ℝ)*base74 + (700828657991743/150000000000000000000000000000 : ℝ)*base75 + (491597170758257/150000000000000000000000000000 : ℝ)*base78 + (1881583271808257/150000000000000000000000000000 : ℝ)*base80 + (628353383/240000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (9232597/10000000000000000000000 : ℝ)*base90 + (9232597/10000000000000000000000 : ℝ)*base92 + (9232597/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1155_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (879/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1155_s7_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080341001/5000000000 : ℝ)*x 0 + (5392823859/10000000000 : ℝ)*x 1 + (1316480927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080341001/5000000000 : ℝ)^2087 ≤ (6565231976967/50000000000000 : ℝ)^1575 := by
    have hnat : (1080341001 : ℕ)^2087*50000000000000^1575 ≤ 6565231976967^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080341001 5000000000 6565231976967 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392823859/10000000000 : ℝ)^2087 ≤ (44119971951479/100000000000000 : ℝ)^1575 := by
    have hnat : (5392823859 : ℕ)^2087*100000000000000^1575 ≤ 44119971951479^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392823859 10000000000 44119971951479 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316480927/2500000000 : ℝ)^2087 ≤ (534369550973/1250000000000 : ℝ)^1575 := by
    have hnat : (1316480927 : ℕ)^2087*1250000000000^1575 ≤ 534369550973^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316480927 2500000000 534369550973 1250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080341001/5000000000 : ℝ), (5392823859/10000000000 : ℝ), (1316480927/2500000000 : ℝ)] ![(6565231976967/50000000000000 : ℝ), (44119971951479/100000000000000 : ℝ), (534369550973/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080341001/5000000000 : ℝ)|^2087 ≤ (6565231976967/50000000000000 : ℝ)^1575
        have hw : |(-1080341001/5000000000 : ℝ)|=(1080341001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392823859/10000000000 : ℝ)|^2087 ≤ (44119971951479/100000000000000 : ℝ)^1575
        have hw : |(5392823859/10000000000 : ℝ)|=(5392823859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316480927/2500000000 : ℝ)|^2087 ≤ (534369550973/1250000000000 : ℝ)^1575
        have hw : |(1316480927/2500000000 : ℝ)|=(1316480927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336178833/2500000000 : ℝ)*x 0 + (-2225045033/10000000000 : ℝ)*x 1 + (1316480929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336178833/2500000000 : ℝ)^2087 ≤ (43599195314841/100000000000000 : ℝ)^1575 := by
    have hnat : (1336178833 : ℕ)^2087*100000000000000^1575 ≤ 43599195314841^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336178833 2500000000 43599195314841 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2225045033/10000000000 : ℝ)^2087 ≤ (13651240513711/100000000000000 : ℝ)^1575 := by
    have hnat : (2225045033 : ℕ)^2087*100000000000000^1575 ≤ 13651240513711^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225045033 10000000000 13651240513711 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316480929/2500000000 : ℝ)^2087 ≤ (21374782081949/50000000000000 : ℝ)^1575 := by
    have hnat : (1316480929 : ℕ)^2087*50000000000000^1575 ≤ 21374782081949^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316480929 2500000000 21374782081949 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336178833/2500000000 : ℝ), (-2225045033/10000000000 : ℝ), (1316480929/2500000000 : ℝ)] ![(43599195314841/100000000000000 : ℝ), (13651240513711/100000000000000 : ℝ), (21374782081949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336178833/2500000000 : ℝ)|^2087 ≤ (43599195314841/100000000000000 : ℝ)^1575
        have hw : |(1336178833/2500000000 : ℝ)|=(1336178833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2225045033/10000000000 : ℝ)|^2087 ≤ (13651240513711/100000000000000 : ℝ)^1575
        have hw : |(-2225045033/10000000000 : ℝ)|=(2225045033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316480929/2500000000 : ℝ)|^2087 ≤ (21374782081949/50000000000000 : ℝ)^1575
        have hw : |(1316480929/2500000000 : ℝ)|=(1316480929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068943067/2000000000 : ℝ)*x 0 + (2632961859/5000000000 : ℝ)*x 1 + (-1112522513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068943067/2000000000 : ℝ)^2087 ≤ (43599195347269/100000000000000 : ℝ)^1575 := by
    have hnat : (1068943067 : ℕ)^2087*100000000000000^1575 ≤ 43599195347269^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068943067 2000000000 43599195347269 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632961859/5000000000 : ℝ)^2087 ≤ (10687391046353/25000000000000 : ℝ)^1575 := by
    have hnat : (2632961859 : ℕ)^2087*25000000000000^1575 ≤ 10687391046353^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632961859 5000000000 10687391046353 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112522513/5000000000 : ℝ)^2087 ≤ (13651240456803/100000000000000 : ℝ)^1575 := by
    have hnat : (1112522513 : ℕ)^2087*100000000000000^1575 ≤ 13651240456803^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112522513 5000000000 13651240456803 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068943067/2000000000 : ℝ), (2632961859/5000000000 : ℝ), (-1112522513/5000000000 : ℝ)] ![(43599195347269/100000000000000 : ℝ), (10687391046353/25000000000000 : ℝ), (13651240456803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068943067/2000000000 : ℝ)|^2087 ≤ (43599195347269/100000000000000 : ℝ)^1575
        have hw : |(1068943067/2000000000 : ℝ)|=(1068943067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632961859/5000000000 : ℝ)|^2087 ≤ (10687391046353/25000000000000 : ℝ)^1575
        have hw : |(2632961859/5000000000 : ℝ)|=(2632961859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112522513/5000000000 : ℝ)|^2087 ≤ (13651240456803/100000000000000 : ℝ)^1575
        have hw : |(-1112522513/5000000000 : ℝ)|=(1112522513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4362843687/10000000000 : ℝ)*x 0 + (2119055209/5000000000 : ℝ)*x 1 + (898243771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362843687/10000000000 : ℝ)^2087 ≤ (33317023937379/100000000000000 : ℝ)^1575 := by
    have hnat : (4362843687 : ℕ)^2087*100000000000000^1575 ≤ 33317023937379^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362843687 10000000000 33317023937379 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119055209/5000000000 : ℝ)^2087 ≤ (6412149811701/20000000000000 : ℝ)^1575 := by
    have hnat : (2119055209 : ℕ)^2087*20000000000000^1575 ≤ 6412149811701^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119055209 5000000000 6412149811701 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898243771/2000000000 : ℝ)^2087 ≤ (17311113497577/50000000000000 : ℝ)^1575 := by
    have hnat : (898243771 : ℕ)^2087*50000000000000^1575 ≤ 17311113497577^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898243771 2000000000 17311113497577 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362843687/10000000000 : ℝ), (2119055209/5000000000 : ℝ), (898243771/2000000000 : ℝ)] ![(33317023937379/100000000000000 : ℝ), (6412149811701/20000000000000 : ℝ), (17311113497577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362843687/10000000000 : ℝ)|^2087 ≤ (33317023937379/100000000000000 : ℝ)^1575
        have hw : |(4362843687/10000000000 : ℝ)|=(4362843687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119055209/5000000000 : ℝ)|^2087 ≤ (6412149811701/20000000000000 : ℝ)^1575
        have hw : |(2119055209/5000000000 : ℝ)|=(2119055209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898243771/2000000000 : ℝ)|^2087 ≤ (17311113497577/50000000000000 : ℝ)^1575
        have hw : |(898243771/2000000000 : ℝ)|=(898243771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080343427/5000000000 : ℝ)*x 0 + (2633121409/5000000000 : ℝ)*x 1 + (5392503599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080343427/5000000000 : ℝ)^2087 ≤ (1641312878089/12500000000000 : ℝ)^1575 := by
    have hnat : (1080343427 : ℕ)^2087*12500000000000^1575 ≤ 1641312878089^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080343427 5000000000 1641312878089 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633121409/5000000000 : ℝ)^2087 ≤ (42752996839969/100000000000000 : ℝ)^1575 := by
    have hnat : (2633121409 : ℕ)^2087*100000000000000^1575 ≤ 42752996839969^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633121409 5000000000 42752996839969 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392503599/10000000000 : ℝ)^2087 ≤ (5514562514247/12500000000000 : ℝ)^1575 := by
    have hnat : (5392503599 : ℕ)^2087*12500000000000^1575 ≤ 5514562514247^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392503599 10000000000 5514562514247 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080343427/5000000000 : ℝ), (2633121409/5000000000 : ℝ), (5392503599/10000000000 : ℝ)] ![(1641312878089/12500000000000 : ℝ), (42752996839969/100000000000000 : ℝ), (5514562514247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080343427/5000000000 : ℝ)|^2087 ≤ (1641312878089/12500000000000 : ℝ)^1575
        have hw : |(-1080343427/5000000000 : ℝ)|=(1080343427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633121409/5000000000 : ℝ)|^2087 ≤ (42752996839969/100000000000000 : ℝ)^1575
        have hw : |(2633121409/5000000000 : ℝ)|=(2633121409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392503599/10000000000 : ℝ)|^2087 ≤ (5514562514247/12500000000000 : ℝ)^1575
        have hw : |(5392503599/10000000000 : ℝ)|=(5392503599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328133439/2500000000 : ℝ)*x 0 + (-1049232573/5000000000 : ℝ)*x 1 + (13481259/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328133439/2500000000 : ℝ)^2087 ≤ (173006709363/400000000000 : ℝ)^1575 := by
    have hnat : (1328133439 : ℕ)^2087*400000000000^1575 ≤ 173006709363^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328133439 2500000000 173006709363 400000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049232573/5000000000 : ℝ)^2087 ≤ (6315911259339/50000000000000 : ℝ)^1575 := by
    have hnat : (1049232573 : ℕ)^2087*50000000000000^1575 ≤ 6315911259339^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049232573 5000000000 6315911259339 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13481259/25000000 : ℝ)^2087 ≤ (2757281257801/6250000000000 : ℝ)^1575 := by
    have hnat : (13481259 : ℕ)^2087*6250000000000^1575 ≤ 2757281257801^1575*25000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13481259 25000000 2757281257801 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328133439/2500000000 : ℝ), (-1049232573/5000000000 : ℝ), (13481259/25000000 : ℝ)] ![(173006709363/400000000000 : ℝ), (6315911259339/50000000000000 : ℝ), (2757281257801/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328133439/2500000000 : ℝ)|^2087 ≤ (173006709363/400000000000 : ℝ)^1575
        have hw : |(1328133439/2500000000 : ℝ)|=(1328133439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049232573/5000000000 : ℝ)|^2087 ≤ (6315911259339/50000000000000 : ℝ)^1575
        have hw : |(-1049232573/5000000000 : ℝ)|=(1049232573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13481259/25000000 : ℝ)|^2087 ≤ (2757281257801/6250000000000 : ℝ)^1575
        have hw : |(13481259/25000000 : ℝ)|=(13481259/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328133439/2500000000 : ℝ)*x 0 + (13481259/25000000 : ℝ)*x 1 + (-1049232573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328133439/2500000000 : ℝ)^2087 ≤ (173006709363/400000000000 : ℝ)^1575 := by
    have hnat : (1328133439 : ℕ)^2087*400000000000^1575 ≤ 173006709363^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328133439 2500000000 173006709363 400000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13481259/25000000 : ℝ)^2087 ≤ (2757281257801/6250000000000 : ℝ)^1575 := by
    have hnat : (13481259 : ℕ)^2087*6250000000000^1575 ≤ 2757281257801^1575*25000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13481259 25000000 2757281257801 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049232573/5000000000 : ℝ)^2087 ≤ (6315911259339/50000000000000 : ℝ)^1575 := by
    have hnat : (1049232573 : ℕ)^2087*50000000000000^1575 ≤ 6315911259339^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049232573 5000000000 6315911259339 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328133439/2500000000 : ℝ), (13481259/25000000 : ℝ), (-1049232573/5000000000 : ℝ)] ![(173006709363/400000000000 : ℝ), (2757281257801/6250000000000 : ℝ), (6315911259339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328133439/2500000000 : ℝ)|^2087 ≤ (173006709363/400000000000 : ℝ)^1575
        have hw : |(1328133439/2500000000 : ℝ)|=(1328133439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13481259/25000000 : ℝ)|^2087 ≤ (2757281257801/6250000000000 : ℝ)^1575
        have hw : |(13481259/25000000 : ℝ)|=(13481259/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049232573/5000000000 : ℝ)|^2087 ≤ (6315911259339/50000000000000 : ℝ)^1575
        have hw : |(-1049232573/5000000000 : ℝ)|=(1049232573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s7_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4260599/9765625 : ℝ)*x 0 + (898116481/2000000000 : ℝ)*x 1 + (1059687293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260599/9765625 : ℝ)^2087 ≤ (6663424396119/20000000000000 : ℝ)^1575 := by
    have hnat : (4260599 : ℕ)^2087*20000000000000^1575 ≤ 6663424396119^1575*9765625^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260599 9765625 6663424396119 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898116481/2000000000 : ℝ)^2087 ≤ (34615725893471/100000000000000 : ℝ)^1575 := by
    have hnat : (898116481 : ℕ)^2087*100000000000000^1575 ≤ 34615725893471^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898116481 2000000000 34615725893471 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059687293/2500000000 : ℝ)^2087 ≤ (32067152118333/100000000000000 : ℝ)^1575 := by
    have hnat : (1059687293 : ℕ)^2087*100000000000000^1575 ≤ 32067152118333^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059687293 2500000000 32067152118333 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260599/9765625 : ℝ), (898116481/2000000000 : ℝ), (1059687293/2500000000 : ℝ)] ![(6663424396119/20000000000000 : ℝ), (34615725893471/100000000000000 : ℝ), (32067152118333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260599/9765625 : ℝ)|^2087 ≤ (6663424396119/20000000000000 : ℝ)^1575
        have hw : |(4260599/9765625 : ℝ)|=(4260599/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898116481/2000000000 : ℝ)|^2087 ≤ (34615725893471/100000000000000 : ℝ)^1575
        have hw : |(898116481/2000000000 : ℝ)|=(898116481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1059687293/2500000000 : ℝ)|^2087 ≤ (32067152118333/100000000000000 : ℝ)^1575
        have hw : |(1059687293/2500000000 : ℝ)|=(1059687293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11369/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14057/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11363/100000 : ℝ) ^ (8347/2048 : ℝ) ≤ (14141267680914421/100000000000000000000 : ℝ) := by
    have hpowers : (11363/100000 : ℝ)^8347 ≤ (14141267680914421/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11363 : ℕ)^8347*100000000000000000000^2048 ≤ 14141267680914421^2048*100000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11363 100000 14141267680914421 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11363/100000 : ℝ)) (X := (14141267680914421/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (879/6250 : ℝ) ^ (8347/2048 : ℝ) ≤ (33725721376539979/100000000000000000000 : ℝ) := by
    have hpowers : (879/6250 : ℝ)^8347 ≤ (33725721376539979/100000000000000000000 : ℝ)^2048 := by
      have hnat : (879 : ℕ)^8347*100000000000000000000^2048 ≤ 33725721376539979^2048*6250^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 6250 33725721376539979 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/6250 : ℝ)) (X := (33725721376539979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014141267680914421/50000000000000000000 : ℝ) ≤ (10000693859496487/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50014141267680914421/50000000000000000000 : ℝ)^2048 ≤ (10000693859496487/10000000000000000 : ℝ)^8347 := by
      have hnat : (50014141267680914421 : ℕ)^2048*10000000000000000^8347 ≤ 10000693859496487^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014141267680914421 50000000000000000000 10000693859496487 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693859496487/10000000000000000 : ℝ)) (X := (50014141267680914421/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (62529916868160909/62500000000000000 : ℝ) ≤ (2500293560239709/2500000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (62529916868160909/62500000000000000 : ℝ)^2048 ≤ (2500293560239709/2500000000000000 : ℝ)^8347 := by
      have hnat : (62529916868160909 : ℕ)^2048*2500000000000000^8347 ≤ 2500293560239709^8347*62500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62529916868160909 62500000000000000 2500293560239709 2500000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500293560239709/2500000000000000 : ℝ)) (X := (62529916868160909/62500000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033725721376539979/50000000000000000000 : ℝ) ≤ (2000330924484237/2000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50033725721376539979/50000000000000000000 : ℝ)^2048 ≤ (2000330924484237/2000000000000000 : ℝ)^8347 := by
      have hnat : (50033725721376539979 : ℕ)^2048*2000000000000000^8347 ≤ 2000330924484237^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033725721376539979 50000000000000000000 2000330924484237 2000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000330924484237/2000000000000000 : ℝ)) (X := (50033725721376539979/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14141267680914421/100000000000000000000 : ℝ) ≤ ((27000956965386668013/27010000000000000000 : ℝ)+2*(480381462349/270100000000000 : ℝ)*(11363/100000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (27000956965386668013/27010000000000000000 : ℝ)+2*(480381462349/270100000000000 : ℝ)*(11363/100000 : ℝ)=(10000693859496487/10000000000000000 : ℝ) by norm_num, show 1+2*(14141267680914421/100000000000000000000 : ℝ)=(50014141267680914421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33725721376539979/100000000000000000000 : ℝ)+(14141267680914421/100000000000000000000 : ℝ) ≤ ((27000956965386668013/27010000000000000000 : ℝ)+(480381462349/270100000000000 : ℝ)*((879/6250 : ℝ)+(11363/100000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (27000956965386668013/27010000000000000000 : ℝ)+(480381462349/270100000000000 : ℝ)*((879/6250 : ℝ)+(11363/100000 : ℝ))=(2500293560239709/2500000000000000 : ℝ) by norm_num, show 1+(33725721376539979/100000000000000000000 : ℝ)+(14141267680914421/100000000000000000000 : ℝ)=(62529916868160909/62500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33725721376539979/100000000000000000000 : ℝ) ≤ ((27000956965386668013/27010000000000000000 : ℝ)+2*(480381462349/270100000000000 : ℝ)*(879/6250 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (27000956965386668013/27010000000000000000 : ℝ)+2*(480381462349/270100000000000 : ℝ)*(879/6250 : ℝ)=(2000330924484237/2000000000000000 : ℝ) by norm_num, show 1+2*(33725721376539979/100000000000000000000 : ℝ)=(50033725721376539979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27000956965386668013/27010000000000000000 : ℝ)*(X 1 0+X 2 0)+(480381462349/270100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (27000956965386668013/27010000000000000000 : ℝ)) (alpha := (480381462349/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27000956965386668013/27010000000000000000 : ℝ)*(X 0 1+X 2 1)+(480381462349/270100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (27000956965386668013/27010000000000000000 : ℝ)) (alpha := (480381462349/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27000956965386668013/27010000000000000000 : ℝ)*(X 0 2+X 1 2)+(480381462349/270100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (27000956965386668013/27010000000000000000 : ℝ)) (alpha := (480381462349/270100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080341001/5000000000 : ℝ)*X 0 0+(5392823859/10000000000 : ℝ)*X 0 1+(1316480927/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336178833/2500000000 : ℝ)*X 1 0+(-2225045033/10000000000 : ℝ)*X 1 1+(1316480929/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068943067/2000000000 : ℝ)*X 2 0+(2632961859/5000000000 : ℝ)*X 2 1+(-1112522513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362843687/10000000000 : ℝ)*X 0 0+(2119055209/5000000000 : ℝ)*X 0 1+(898243771/2000000000 : ℝ)*X 0 2+(4362843687/10000000000 : ℝ)*X 1 0+(2119055209/5000000000 : ℝ)*X 1 1+(898243771/2000000000 : ℝ)*X 1 2+(4362843687/10000000000 : ℝ)*X 2 0+(2119055209/5000000000 : ℝ)*X 2 1+(898243771/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1080343427/5000000000 : ℝ)*X 0 0+(2633121409/5000000000 : ℝ)*X 0 1+(5392503599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328133439/2500000000 : ℝ)*X 1 0+(-1049232573/5000000000 : ℝ)*X 1 1+(13481259/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328133439/2500000000 : ℝ)*X 2 0+(13481259/25000000 : ℝ)*X 2 1+(-1049232573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260599/9765625 : ℝ)*X 0 0+(898116481/2000000000 : ℝ)*X 0 1+(1059687293/2500000000 : ℝ)*X 0 2+(4260599/9765625 : ℝ)*X 1 0+(898116481/2000000000 : ℝ)*X 1 1+(1059687293/2500000000 : ℝ)*X 1 2+(4260599/9765625 : ℝ)*X 2 0+(898116481/2000000000 : ℝ)*X 2 1+(1059687293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64621282792591898025771/6752500000000000000000000000 : ℝ) := by norm_num
    linear_combination (75700683/4000000000000 : ℝ)*(base19) + (887839751/50000000000000 : ℝ)*(base23) + (32405227/50000000000000 : ℝ)*(lower2) + (117824241/50000000000000 : ℝ)*(upper3) + (78927859/50000000000000 : ℝ)*(upper5) + (5915623686430961/100000000000000 : ℝ)*(major0) + (5915623686430961/100000000000000 : ℝ)*(major1) + (5915623686430961/100000000000000 : ℝ)*(major2) + (7880265561255607/100000000000000 : ℝ)*(sp0) + (1576063266033527/20000000000000 : ℝ)*(sp1) + (985039555875651/12500000000000 : ℝ)*(sp2) + (790180223306767/20000000000000 : ℝ)*(sp3) + (3291339319/6250000000000 : ℝ)*(sp4) + (5542928813/20000000000000 : ℝ)*(sp7) + (39509288311779/1000000000000 : ℝ)*(f.failure) + (788031822268471/10000000000000 : ℝ)*(f.sum) + (4479561375193/6752500000000000000000000000 : ℝ)*base66 + (15884789958650450493/2701000000000000000000000000000000 : ℝ)*base67 + (18903893724566549507/2701000000000000000000000000000000 : ℝ)*base70 + (67364273487914549507/2701000000000000000000000000000000 : ℝ)*base72 + (93238839175389/13505000000000000000000000000 : ℝ)*base73 + (71715856578225450493/2701000000000000000000000000000000 : ℝ)*base75 + (5532400394774549507/2701000000000000000000000000000000 : ℝ)*base78 + (51285660218491450493/2701000000000000000000000000000000 : ℝ)*base79 + (14365409165149/3376250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (655157/100000000000000000000 : ℝ)*base90 + (655157/100000000000000000000 : ℝ)*base92 + (655157/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3435952605745722751105544943/1350500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469125611/100000000000000 : ℝ)*(base19) + (102090689/20000000000000 : ℝ)*(base23) + (52064421/100000000000000 : ℝ)*(upper3) + (4683529/25000000000000 : ℝ)*(lower4) + (52348143/100000000000000 : ℝ)*(upper5) + (5945498487428179/100000000000000 : ℝ)*(major0) + (5945498487428179/100000000000000 : ℝ)*(major1) + (5945498487428179/100000000000000 : ℝ)*(major2) + (13025533057/100000000000000 : ℝ)*(sp1) + (7013275001/50000000000000 : ℝ)*(sp2) + (792011526625959/10000000000000 : ℝ)*(sp4) + (3960050885800461/50000000000000 : ℝ)*(sp5) + (7920100729256143/100000000000000 : ℝ)*(sp6) + (992720405947459/25000000000000 : ℝ)*(sp7) + (992720405947459/25000000000000 : ℝ)*(f.failure) + (792011526625959/10000000000000 : ℝ)*(f.sum) + (65765945575909/13505000000000000000000000000 : ℝ)*base66 + (8633700592498761673/2701000000000000000000000000000000 : ℝ)*base68 + (19599004317900761673/2701000000000000000000000000000000 : ℝ)*base70 + (26426211519990761673/2701000000000000000000000000000000 : ℝ)*base72 + (2857837827183/1688125000000000000000000000 : ℝ)*base74 + (35003711077902761673/2701000000000000000000000000000000 : ℝ)*base76 + (4237741830212761673/2701000000000000000000000000000000 : ℝ)*base78 + (36003575393314761673/2701000000000000000000000000000000 : ℝ)*base80 + (43105600673839/13505000000000000000000000000 : ℝ)*base82 + (1216597/2500000000000000000000 : ℝ)*base90 + (1216597/2500000000000000000000 : ℝ)*base92 + (1216597/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1155_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1155_s8_0 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080344939/5000000000 : ℝ)*x 0 + (1078551569/2000000000 : ℝ)*x 1 + (5265984339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080344939/5000000000 : ℝ)^2087 ≤ (3282631843879/25000000000000 : ℝ)^1575 := by
    have hnat : (1080344939 : ℕ)^2087*25000000000000^1575 ≤ 3282631843879^1575*5000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080344939 5000000000 3282631843879 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078551569/2000000000 : ℝ)^2087 ≤ (2757453519317/6250000000000 : ℝ)^1575 := by
    have hnat : (1078551569 : ℕ)^2087*6250000000000^1575 ≤ 2757453519317^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078551569 2000000000 2757453519317 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265984339/10000000000 : ℝ)^2087 ≤ (42750216298517/100000000000000 : ℝ)^1575 := by
    have hnat : (5265984339 : ℕ)^2087*100000000000000^1575 ≤ 42750216298517^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265984339 10000000000 42750216298517 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080344939/5000000000 : ℝ), (1078551569/2000000000 : ℝ), (5265984339/10000000000 : ℝ)] ![(3282631843879/25000000000000 : ℝ), (2757453519317/6250000000000 : ℝ), (42750216298517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080344939/5000000000 : ℝ)|^2087 ≤ (3282631843879/25000000000000 : ℝ)^1575
        have hw : |(-1080344939/5000000000 : ℝ)|=(1080344939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078551569/2000000000 : ℝ)|^2087 ≤ (2757453519317/6250000000000 : ℝ)^1575
        have hw : |(1078551569/2000000000 : ℝ)|=(1078551569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265984339/10000000000 : ℝ)|^2087 ≤ (42750216298517/100000000000000 : ℝ)^1575
        have hw : |(5265984339/10000000000 : ℝ)|=(5265984339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_1 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344698159/10000000000 : ℝ)*x 0 + (-55624693/250000000 : ℝ)*x 1 + (1053196857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344698159/10000000000 : ℝ)^2087 ≤ (5449876210949/12500000000000 : ℝ)^1575 := by
    have hnat : (5344698159 : ℕ)^2087*12500000000000^1575 ≤ 5449876210949^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344698159 10000000000 5449876210949 12500000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55624693/250000000 : ℝ)^2087 ≤ (13650774577431/100000000000000 : ℝ)^1575 := by
    have hnat : (55624693 : ℕ)^2087*100000000000000^1575 ≤ 13650774577431^1575*250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55624693 250000000 13650774577431 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053196857/2000000000 : ℝ)^2087 ≤ (21375107858813/50000000000000 : ℝ)^1575 := by
    have hnat : (1053196857 : ℕ)^2087*50000000000000^1575 ≤ 21375107858813^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053196857 2000000000 21375107858813 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344698159/10000000000 : ℝ), (-55624693/250000000 : ℝ), (1053196857/2000000000 : ℝ)] ![(5449876210949/12500000000000 : ℝ), (13650774577431/100000000000000 : ℝ), (21375107858813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344698159/10000000000 : ℝ)|^2087 ≤ (5449876210949/12500000000000 : ℝ)^1575
        have hw : |(5344698159/10000000000 : ℝ)|=(5344698159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55624693/250000000 : ℝ)|^2087 ≤ (13650774577431/100000000000000 : ℝ)^1575
        have hw : |(-55624693/250000000 : ℝ)|=(55624693/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053196857/2000000000 : ℝ)|^2087 ≤ (21375107858813/50000000000000 : ℝ)^1575
        have hw : |(1053196857/2000000000 : ℝ)|=(1053196857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_2 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668087257/1250000000 : ℝ)*x 0 + (5265984341/10000000000 : ℝ)*x 1 + (-278123473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668087257/1250000000 : ℝ)^2087 ≤ (43599008574239/100000000000000 : ℝ)^1575 := by
    have hnat : (668087257 : ℕ)^2087*100000000000000^1575 ≤ 43599008574239^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668087257 1250000000 43599008574239 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265984341/10000000000 : ℝ)^2087 ≤ (42750216320031/100000000000000 : ℝ)^1575 := by
    have hnat : (5265984341 : ℕ)^2087*100000000000000^1575 ≤ 42750216320031^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265984341 10000000000 42750216320031 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278123473/1250000000 : ℝ)^2087 ≤ (13650775097729/100000000000000 : ℝ)^1575 := by
    have hnat : (278123473 : ℕ)^2087*100000000000000^1575 ≤ 13650775097729^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278123473 1250000000 13650775097729 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668087257/1250000000 : ℝ), (5265984341/10000000000 : ℝ), (-278123473/1250000000 : ℝ)] ![(43599008574239/100000000000000 : ℝ), (42750216320031/100000000000000 : ℝ), (13650775097729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668087257/1250000000 : ℝ)|^2087 ≤ (43599008574239/100000000000000 : ℝ)^1575
        have hw : |(668087257/1250000000 : ℝ)|=(668087257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265984341/10000000000 : ℝ)|^2087 ≤ (42750216320031/100000000000000 : ℝ)^1575
        have hw : |(5265984341/10000000000 : ℝ)|=(5265984341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278123473/1250000000 : ℝ)|^2087 ≤ (13650775097729/100000000000000 : ℝ)^1575
        have hw : |(-278123473/1250000000 : ℝ)|=(278123473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_3 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4362847001/10000000000 : ℝ)*x 0 + (4238236247/10000000000 : ℝ)*x 1 + (1122773023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362847001/10000000000 : ℝ)^2087 ≤ (16658528735907/50000000000000 : ℝ)^1575 := by
    have hnat : (4362847001 : ℕ)^2087*50000000000000^1575 ≤ 16658528735907^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362847001 10000000000 16658528735907 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238236247/10000000000 : ℝ)^2087 ≤ (6412402076193/20000000000000 : ℝ)^1575 := by
    have hnat : (4238236247 : ℕ)^2087*20000000000000^1575 ≤ 6412402076193^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238236247 10000000000 6412402076193 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122773023/2500000000 : ℝ)^2087 ≤ (17310466067021/50000000000000 : ℝ)^1575 := by
    have hnat : (1122773023 : ℕ)^2087*50000000000000^1575 ≤ 17310466067021^1575*2500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122773023 2500000000 17310466067021 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362847001/10000000000 : ℝ), (4238236247/10000000000 : ℝ), (1122773023/2500000000 : ℝ)] ![(16658528735907/50000000000000 : ℝ), (6412402076193/20000000000000 : ℝ), (17310466067021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362847001/10000000000 : ℝ)|^2087 ≤ (16658528735907/50000000000000 : ℝ)^1575
        have hw : |(4362847001/10000000000 : ℝ)|=(4362847001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238236247/10000000000 : ℝ)|^2087 ≤ (6412402076193/20000000000000 : ℝ)^1575
        have hw : |(4238236247/10000000000 : ℝ)|=(4238236247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122773023/2500000000 : ℝ)|^2087 ≤ (17310466067021/50000000000000 : ℝ)^1575
        have hw : |(1122773023/2500000000 : ℝ)|=(1122773023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_4 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-21606947/100000000 : ℝ)*x 0 + (263315141/500000000 : ℝ)*x 1 + (539243823/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21606947/100000000 : ℝ)^2087 ≤ (2626113240953/20000000000000 : ℝ)^1575 := by
    have hnat : (21606947 : ℕ)^2087*20000000000000^1575 ≤ 2626113240953^1575*100000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21606947 100000000 2626113240953 20000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263315141/500000000 : ℝ)^2087 ≤ (2137682115353/5000000000000 : ℝ)^1575 := by
    have hnat : (263315141 : ℕ)^2087*5000000000000^1575 ≤ 2137682115353^1575*500000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263315141 500000000 2137682115353 5000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539243823/1000000000 : ℝ)^2087 ≤ (44115791477531/100000000000000 : ℝ)^1575 := by
    have hnat : (539243823 : ℕ)^2087*100000000000000^1575 ≤ 44115791477531^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539243823 1000000000 44115791477531 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21606947/100000000 : ℝ), (263315141/500000000 : ℝ), (539243823/1000000000 : ℝ)] ![(2626113240953/20000000000000 : ℝ), (2137682115353/5000000000000 : ℝ), (44115791477531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21606947/100000000 : ℝ)|^2087 ≤ (2626113240953/20000000000000 : ℝ)^1575
        have hw : |(-21606947/100000000 : ℝ)|=(21606947/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263315141/500000000 : ℝ)|^2087 ≤ (2137682115353/5000000000000 : ℝ)^1575
        have hw : |(263315141/500000000 : ℝ)|=(263315141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539243823/1000000000 : ℝ)|^2087 ≤ (44115791477531/100000000000000 : ℝ)^1575
        have hw : |(539243823/1000000000 : ℝ)|=(539243823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_5 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531254863/1000000000 : ℝ)*x 0 + (-209853387/1000000000 : ℝ)*x 1 + (674054779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531254863/1000000000 : ℝ)^2087 ≤ (43251837802349/100000000000000 : ℝ)^1575 := by
    have hnat : (531254863 : ℕ)^2087*100000000000000^1575 ≤ 43251837802349^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531254863 1000000000 43251837802349 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209853387/1000000000 : ℝ)^2087 ≤ (6316185345363/50000000000000 : ℝ)^1575 := by
    have hnat : (209853387 : ℕ)^2087*50000000000000^1575 ≤ 6316185345363^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209853387 1000000000 6316185345363 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674054779/1250000000 : ℝ)^2087 ≤ (11028947874803/25000000000000 : ℝ)^1575 := by
    have hnat : (674054779 : ℕ)^2087*25000000000000^1575 ≤ 11028947874803^1575*1250000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674054779 1250000000 11028947874803 25000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531254863/1000000000 : ℝ), (-209853387/1000000000 : ℝ), (674054779/1250000000 : ℝ)] ![(43251837802349/100000000000000 : ℝ), (6316185345363/50000000000000 : ℝ), (11028947874803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531254863/1000000000 : ℝ)|^2087 ≤ (43251837802349/100000000000000 : ℝ)^1575
        have hw : |(531254863/1000000000 : ℝ)|=(531254863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209853387/1000000000 : ℝ)|^2087 ≤ (6316185345363/50000000000000 : ℝ)^1575
        have hw : |(-209853387/1000000000 : ℝ)|=(209853387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674054779/1250000000 : ℝ)|^2087 ≤ (11028947874803/25000000000000 : ℝ)^1575
        have hw : |(674054779/1250000000 : ℝ)|=(674054779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_6 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531254863/1000000000 : ℝ)*x 0 + (5392438231/10000000000 : ℝ)*x 1 + (-209853387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531254863/1000000000 : ℝ)^2087 ≤ (43251837802349/100000000000000 : ℝ)^1575 := by
    have hnat : (531254863 : ℕ)^2087*100000000000000^1575 ≤ 43251837802349^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531254863 1000000000 43251837802349 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392438231/10000000000 : ℝ)^2087 ≤ (44115791488371/100000000000000 : ℝ)^1575 := by
    have hnat : (5392438231 : ℕ)^2087*100000000000000^1575 ≤ 44115791488371^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392438231 10000000000 44115791488371 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209853387/1000000000 : ℝ)^2087 ≤ (6316185345363/50000000000000 : ℝ)^1575 := by
    have hnat : (209853387 : ℕ)^2087*50000000000000^1575 ≤ 6316185345363^1575*1000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209853387 1000000000 6316185345363 50000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531254863/1000000000 : ℝ), (5392438231/10000000000 : ℝ), (-209853387/1000000000 : ℝ)] ![(43251837802349/100000000000000 : ℝ), (44115791488371/100000000000000 : ℝ), (6316185345363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531254863/1000000000 : ℝ)|^2087 ≤ (43251837802349/100000000000000 : ℝ)^1575
        have hw : |(531254863/1000000000 : ℝ)|=(531254863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392438231/10000000000 : ℝ)|^2087 ≤ (44115791488371/100000000000000 : ℝ)^1575
        have hw : |(5392438231/10000000000 : ℝ)|=(5392438231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209853387/1000000000 : ℝ)|^2087 ≤ (6316185345363/50000000000000 : ℝ)^1575
        have hw : |(-209853387/1000000000 : ℝ)|=(209853387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1155_s8_7 (p : ℝ) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4362856561/10000000000 : ℝ)*x 0 + (898091391/2000000000 : ℝ)*x 1 + (4238873781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362856561/10000000000 : ℝ)^2087 ≤ (333171542097/1000000000000 : ℝ)^1575 := by
    have hnat : (4362856561 : ℕ)^2087*1000000000000^1575 ≤ 333171542097^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362856561 10000000000 333171542097 1000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898091391/2000000000 : ℝ)^2087 ≤ (34614444503391/100000000000000 : ℝ)^1575 := by
    have hnat : (898091391 : ℕ)^2087*100000000000000^1575 ≤ 34614444503391^1575*2000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898091391 2000000000 34614444503391 100000000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238873781/10000000000 : ℝ)^2087 ≤ (2004275079533/6250000000000 : ℝ)^1575 := by
    have hnat : (4238873781 : ℕ)^2087*6250000000000^1575 ≤ 2004275079533^1575*10000000000^2087 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238873781 10000000000 2004275079533 6250000000000 2087 1575 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2087/512 : ℝ)) 2087 1575 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362856561/10000000000 : ℝ), (898091391/2000000000 : ℝ), (4238873781/10000000000 : ℝ)] ![(333171542097/1000000000000 : ℝ), (34614444503391/100000000000000 : ℝ), (2004275079533/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362856561/10000000000 : ℝ)|^2087 ≤ (333171542097/1000000000000 : ℝ)^1575
        have hw : |(4362856561/10000000000 : ℝ)|=(4362856561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898091391/2000000000 : ℝ)|^2087 ≤ (34614444503391/100000000000000 : ℝ)^1575
        have hw : |(898091391/2000000000 : ℝ)|=(898091391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238873781/10000000000 : ℝ)|^2087 ≤ (2004275079533/6250000000000 : ℝ)^1575
        have hw : |(4238873781/10000000000 : ℝ)|=(4238873781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1155_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11371/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11369/100000 : ℝ) ^ (8347/2048 : ℝ) ≤ (177146569529657/1250000000000000000 : ℝ) := by
    have hpowers : (11369/100000 : ℝ)^8347 ≤ (177146569529657/1250000000000000000 : ℝ)^2048 := by
      have hnat : (11369 : ℕ)^8347*1250000000000000000^2048 ≤ 177146569529657^2048*100000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11369 100000 177146569529657 1250000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11369/100000 : ℝ)) (X := (177146569529657/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14057/100000 : ℝ) ^ (8347/2048 : ℝ) ≤ (33657358794108071/100000000000000000000 : ℝ) := by
    have hpowers : (14057/100000 : ℝ)^8347 ≤ (33657358794108071/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14057 : ℕ)^8347*100000000000000000000^2048 ≤ 33657358794108071^2048*100000^8347 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14057 100000 33657358794108071 100000000000000000000 8347 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14057/100000 : ℝ)) (X := (33657358794108071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (625177146569529657/625000000000000000 : ℝ) ≤ (2000139070758369/2000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (625177146569529657/625000000000000000 : ℝ)^2048 ≤ (2000139070758369/2000000000000000 : ℝ)^8347 := by
      have hnat : (625177146569529657 : ℕ)^2048*2000000000000000^8347 ≤ 2000139070758369^8347*625000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625177146569529657 625000000000000000 2000139070758369 2000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000139070758369/2000000000000000 : ℝ)) (X := (625177146569529657/625000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047829084356480631/100000000000000000000 : ℝ) ≤ (10001173311273811/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (100047829084356480631/100000000000000000000 : ℝ)^2048 ≤ (10001173311273811/10000000000000000 : ℝ)^8347 := by
      have hnat : (100047829084356480631 : ℕ)^2048*10000000000000000^8347 ≤ 10001173311273811^8347*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047829084356480631 100000000000000000000 10001173311273811 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001173311273811/10000000000000000 : ℝ)) (X := (100047829084356480631/100000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033657358794108071/50000000000000000000 : ℝ) ≤ (10001651268755777/10000000000000000 : ℝ) ^ (8347/2048 : ℝ) := by
    have hpowers : (50033657358794108071/50000000000000000000 : ℝ)^2048 ≤ (10001651268755777/10000000000000000 : ℝ)^8347 := by
      have hnat : (50033657358794108071 : ℕ)^2048*10000000000000000^8347 ≤ 10001651268755777^8347*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033657358794108071 50000000000000000000 10001651268755777 10000000000000000 2048 8347 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001651268755777/10000000000000000 : ℝ)) (X := (50033657358794108071/50000000000000000000 : ℝ)) (by norm_num) 8347 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(177146569529657/1250000000000000000 : ℝ) ≤ ((6717750328441884113/6720000000000000000 : ℝ)+2*(238978740983/134400000000000 : ℝ)*(11369/100000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (6717750328441884113/6720000000000000000 : ℝ)+2*(238978740983/134400000000000 : ℝ)*(11369/100000 : ℝ)=(2000139070758369/2000000000000000 : ℝ) by norm_num, show 1+2*(177146569529657/1250000000000000000 : ℝ)=(625177146569529657/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33657358794108071/100000000000000000000 : ℝ)+(177146569529657/1250000000000000000 : ℝ) ≤ ((6717750328441884113/6720000000000000000 : ℝ)+(238978740983/134400000000000 : ℝ)*((14057/100000 : ℝ)+(11369/100000 : ℝ)))^(8347/2048 : ℝ) := by
    rw [show (6717750328441884113/6720000000000000000 : ℝ)+(238978740983/134400000000000 : ℝ)*((14057/100000 : ℝ)+(11369/100000 : ℝ))=(10001173311273811/10000000000000000 : ℝ) by norm_num, show 1+(33657358794108071/100000000000000000000 : ℝ)+(177146569529657/1250000000000000000 : ℝ)=(100047829084356480631/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33657358794108071/100000000000000000000 : ℝ) ≤ ((6717750328441884113/6720000000000000000 : ℝ)+2*(238978740983/134400000000000 : ℝ)*(14057/100000 : ℝ))^(8347/2048 : ℝ) := by
    rw [show (6717750328441884113/6720000000000000000 : ℝ)+2*(238978740983/134400000000000 : ℝ)*(14057/100000 : ℝ)=(10001651268755777/10000000000000000 : ℝ) by norm_num, show 1+2*(33657358794108071/100000000000000000000 : ℝ)=(50033657358794108071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6717750328441884113/6720000000000000000 : ℝ)*(X 1 0+X 2 0)+(238978740983/134400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (6717750328441884113/6720000000000000000 : ℝ)) (alpha := (238978740983/134400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6717750328441884113/6720000000000000000 : ℝ)*(X 0 1+X 2 1)+(238978740983/134400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (6717750328441884113/6720000000000000000 : ℝ)) (alpha := (238978740983/134400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6717750328441884113/6720000000000000000 : ℝ)*(X 0 2+X 1 2)+(238978740983/134400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8347/2048 : ℝ)) (lo := (11369/100000 : ℝ)) (hi := (14057/100000 : ℝ)) (c := (6717750328441884113/6720000000000000000 : ℝ)) (alpha := (238978740983/134400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080344939/5000000000 : ℝ)*X 0 0+(1078551569/2000000000 : ℝ)*X 0 1+(5265984339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344698159/10000000000 : ℝ)*X 1 0+(-55624693/250000000 : ℝ)*X 1 1+(1053196857/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668087257/1250000000 : ℝ)*X 2 0+(5265984341/10000000000 : ℝ)*X 2 1+(-278123473/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362847001/10000000000 : ℝ)*X 0 0+(4238236247/10000000000 : ℝ)*X 0 1+(1122773023/2500000000 : ℝ)*X 0 2+(4362847001/10000000000 : ℝ)*X 1 0+(4238236247/10000000000 : ℝ)*X 1 1+(1122773023/2500000000 : ℝ)*X 1 2+(4362847001/10000000000 : ℝ)*X 2 0+(4238236247/10000000000 : ℝ)*X 2 1+(1122773023/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21606947/100000000 : ℝ)*X 0 0+(263315141/500000000 : ℝ)*X 0 1+(539243823/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531254863/1000000000 : ℝ)*X 1 0+(-209853387/1000000000 : ℝ)*X 1 1+(674054779/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531254863/1000000000 : ℝ)*X 2 0+(5392438231/10000000000 : ℝ)*X 2 1+(-209853387/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362856561/10000000000 : ℝ)*X 0 0+(898091391/2000000000 : ℝ)*X 0 1+(4238873781/10000000000 : ℝ)*X 0 2+(4362856561/10000000000 : ℝ)*X 1 0+(898091391/2000000000 : ℝ)*X 1 1+(4238873781/10000000000 : ℝ)*X 1 2+(4362856561/10000000000 : ℝ)*X 2 0+(898091391/2000000000 : ℝ)*X 2 1+(4238873781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1155_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (276330500487898536163562283/112000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (811685541/100000000000000 : ℝ)*(base19) + (619841029/100000000000000 : ℝ)*(base23) + (7820471/25000000000000 : ℝ)*(lower2) + (19983447/12500000000000 : ℝ)*(upper3) + (4997211/50000000000000 : ℝ)*(lower4) + (5921481001083909/100000000000000 : ℝ)*(major0) + (5921481001083909/100000000000000 : ℝ)*(major1) + (5921481001083909/100000000000000 : ℝ)*(major2) + (246503335231301/3125000000000 : ℝ)*(sp0) + (1577624058337957/20000000000000 : ℝ)*(sp1) + (7888120483534297/100000000000000 : ℝ)*(sp2) + (197741517127599/5000000000000 : ℝ)*(sp3) + (7187986847/50000000000000 : ℝ)*(sp4) + (10473999279/100000000000000 : ℝ)*(sp7) + (197742040827563/5000000000000 : ℝ)*(f.failure) + (3944060551687663/50000000000000 : ℝ)*(f.sum) + (18336220862129/2240000000000000000000000000 : ℝ)*base65 + (139092242098129239/224000000000000000000000000000000 : ℝ)*base67 + (5023785358450129239/224000000000000000000000000000000 : ℝ)*base69 + (1634150600237870761/224000000000000000000000000000000 : ℝ)*base72 + (9291133337649/2240000000000000000000000000 : ℝ)*base73 + (5778650606482129239/224000000000000000000000000000000 : ℝ)*base75 + (2779406336754129239/224000000000000000000000000000000 : ℝ)*base77 + (2984951345069870761/224000000000000000000000000000000 : ℝ)*base80 + (2617716588209/2240000000000000000000000000 : ℝ)*base81 + (5394771/500000000000000000000 : ℝ)*base89 + (5394771/500000000000000000000 : ℝ)*base91 + (5394771/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69326645805179763392925231/11200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141016103/12500000000000 : ℝ)*(base19) + (1227494123/100000000000000 : ℝ)*(base23) + (396736699/100000000000000 : ℝ)*(lower1) + (62320613/50000000000000 : ℝ)*(upper3) + (11316033/25000000000000 : ℝ)*(lower4) + (126394111/100000000000000 : ℝ)*(upper5) + (595138398490113/10000000000000 : ℝ)*(major0) + (595138398490113/10000000000000 : ℝ)*(major1) + (595138398490113/10000000000000 : ℝ)*(major2) + (146273533/6250000000000 : ℝ)*(sp2) + (1585591066311593/20000000000000 : ℝ)*(sp4) + (7927954203429141/100000000000000 : ℝ)*(sp5) + (1585590352737463/20000000000000 : ℝ)*(sp6) + (62106444248671/1562500000000 : ℝ)*(sp7) + (62106444248671/1562500000000 : ℝ)*(f.failure) + (1585591066311593/20000000000000 : ℝ)*(f.sum) + (1166386773123/224000000000000000000000000 : ℝ)*base66 + (3566383869375925077/22400000000000000000000000000000 : ℝ)*base68 + (4830470598474923/22400000000000000000000000000000 : ℝ)*base69 + (2533111992518474923/22400000000000000000000000000000 : ℝ)*base71 + (1025751647293/224000000000000000000000000 : ℝ)*base73 + (2255933775129674923/22400000000000000000000000000000 : ℝ)*base75 + (198144253907274923/22400000000000000000000000000000 : ℝ)*base77 + (819129743267125077/22400000000000000000000000000000 : ℝ)*base80 + (271824536999/44800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1112193/156250000000000000000 : ℝ)*base90 + (1112193/156250000000000000000 : ℝ)*base92 + (1112193/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1155_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1155_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1155_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1155_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1155_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1155_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8347/2048 : ℝ) ≤ p) (hpb : p ≤ (2087/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149727417/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5667/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11371/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1155_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
