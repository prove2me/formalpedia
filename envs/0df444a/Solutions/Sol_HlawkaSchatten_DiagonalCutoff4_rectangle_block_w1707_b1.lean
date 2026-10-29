-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1707_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:00.865645+00:00
-- url     : https://prove2.me/submissions/9d046b62-d4e9-4ebe-8e7e-9e8b9725f916

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
theorem support_rectangle_w1707_s3_0 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1422987453/10000000000 : ℝ)*x 0 + (5471953887/10000000000 : ℝ)*x 1 + (321119567/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1422987453/10000000000 : ℝ)^5279 ≤ (8900452612271/100000000000000 : ℝ)^4255 := by
    have hnat : (1422987453 : ℕ)^5279*100000000000000^4255 ≤ 8900452612271^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422987453 10000000000 8900452612271 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471953887/10000000000 : ℝ)^5279 ≤ (47328669586773/100000000000000 : ℝ)^4255 := by
    have hnat : (5471953887 : ℕ)^5279*100000000000000^4255 ≤ 47328669586773^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471953887 10000000000 47328669586773 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321119567/625000000 : ℝ)^5279 ≤ (4377087779001/10000000000000 : ℝ)^4255 := by
    have hnat : (321119567 : ℕ)^5279*10000000000000^4255 ≤ 4377087779001^4255*625000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321119567 625000000 4377087779001 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1422987453/10000000000 : ℝ), (5471953887/10000000000 : ℝ), (321119567/625000000 : ℝ)] ![(8900452612271/100000000000000 : ℝ), (47328669586773/100000000000000 : ℝ), (4377087779001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1422987453/10000000000 : ℝ)|^5279 ≤ (8900452612271/100000000000000 : ℝ)^4255
        have hw : |(-1422987453/10000000000 : ℝ)|=(1422987453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471953887/10000000000 : ℝ)|^5279 ≤ (47328669586773/100000000000000 : ℝ)^4255
        have hw : |(5471953887/10000000000 : ℝ)|=(5471953887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(321119567/625000000 : ℝ)|^5279 ≤ (4377087779001/10000000000000 : ℝ)^4255
        have hw : |(321119567/625000000 : ℝ)|=(321119567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_1 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344525031/10000000000 : ℝ)*x 0 + (-1596239863/10000000000 : ℝ)*x 1 + (5137913239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344525031/10000000000 : ℝ)^5279 ≤ (11491276180223/25000000000000 : ℝ)^4255 := by
    have hnat : (5344525031 : ℕ)^5279*25000000000000^4255 ≤ 11491276180223^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344525031 10000000000 11491276180223 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1596239863/10000000000 : ℝ)^5279 ≤ (5132007854727/50000000000000 : ℝ)^4255 := by
    have hnat : (1596239863 : ℕ)^5279*50000000000000^4255 ≤ 5132007854727^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596239863 10000000000 5132007854727 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137913239/10000000000 : ℝ)^5279 ≤ (43770879555101/100000000000000 : ℝ)^4255 := by
    have hnat : (5137913239 : ℕ)^5279*100000000000000^4255 ≤ 43770879555101^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137913239 10000000000 43770879555101 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344525031/10000000000 : ℝ), (-1596239863/10000000000 : ℝ), (5137913239/10000000000 : ℝ)] ![(11491276180223/25000000000000 : ℝ), (5132007854727/50000000000000 : ℝ), (43770879555101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344525031/10000000000 : ℝ)|^5279 ≤ (11491276180223/25000000000000 : ℝ)^4255
        have hw : |(5344525031/10000000000 : ℝ)|=(5344525031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1596239863/10000000000 : ℝ)|^5279 ≤ (5132007854727/50000000000000 : ℝ)^4255
        have hw : |(-1596239863/10000000000 : ℝ)|=(1596239863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137913239/10000000000 : ℝ)|^5279 ≤ (43770879555101/100000000000000 : ℝ)^4255
        have hw : |(5137913239/10000000000 : ℝ)|=(5137913239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_2 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344525289/10000000000 : ℝ)*x 0 + (2568956623/5000000000 : ℝ)*x 1 + (-1596239509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344525289/10000000000 : ℝ)^5279 ≤ (9193021494759/20000000000000 : ℝ)^4255 := by
    have hnat : (5344525289 : ℕ)^5279*20000000000000^4255 ≤ 9193021494759^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344525289 10000000000 9193021494759 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568956623/5000000000 : ℝ)^5279 ≤ (21885439814543/50000000000000 : ℝ)^4255 := by
    have hnat : (2568956623 : ℕ)^5279*50000000000000^4255 ≤ 21885439814543^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568956623 5000000000 21885439814543 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596239509/10000000000 : ℝ)^5279 ≤ (1026401288539/10000000000000 : ℝ)^4255 := by
    have hnat : (1596239509 : ℕ)^5279*10000000000000^4255 ≤ 1026401288539^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596239509 10000000000 1026401288539 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344525289/10000000000 : ℝ), (2568956623/5000000000 : ℝ), (-1596239509/10000000000 : ℝ)] ![(9193021494759/20000000000000 : ℝ), (21885439814543/50000000000000 : ℝ), (1026401288539/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344525289/10000000000 : ℝ)|^5279 ≤ (9193021494759/20000000000000 : ℝ)^4255
        have hw : |(5344525289/10000000000 : ℝ)|=(5344525289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568956623/5000000000 : ℝ)|^5279 ≤ (21885439814543/50000000000000 : ℝ)^4255
        have hw : |(2568956623/5000000000 : ℝ)|=(2568956623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1596239509/10000000000 : ℝ)|^5279 ≤ (1026401288539/10000000000000 : ℝ)^4255
        have hw : |(-1596239509/10000000000 : ℝ)|=(1596239509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_3 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4108577507/10000000000 : ℝ)*x 0 + (3645604647/10000000000 : ℝ)*x 1 + (2303720119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4108577507/10000000000 : ℝ)^5279 ≤ (8292075333931/25000000000000 : ℝ)^4255 := by
    have hnat : (4108577507 : ℕ)^5279*25000000000000^4255 ≤ 8292075333931^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108577507 10000000000 8292075333931 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3645604647/10000000000 : ℝ)^5279 ≤ (14298019757287/50000000000000 : ℝ)^4255 := by
    have hnat : (3645604647 : ℕ)^5279*50000000000000^4255 ≤ 14298019757287^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3645604647 10000000000 14298019757287 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303720119/5000000000 : ℝ)^5279 ≤ (3823565913379/10000000000000 : ℝ)^4255 := by
    have hnat : (2303720119 : ℕ)^5279*10000000000000^4255 ≤ 3823565913379^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303720119 5000000000 3823565913379 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4108577507/10000000000 : ℝ), (3645604647/10000000000 : ℝ), (2303720119/5000000000 : ℝ)] ![(8292075333931/25000000000000 : ℝ), (14298019757287/50000000000000 : ℝ), (3823565913379/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4108577507/10000000000 : ℝ)|^5279 ≤ (8292075333931/25000000000000 : ℝ)^4255
        have hw : |(4108577507/10000000000 : ℝ)|=(4108577507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3645604647/10000000000 : ℝ)|^5279 ≤ (14298019757287/50000000000000 : ℝ)^4255
        have hw : |(3645604647/10000000000 : ℝ)|=(3645604647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2303720119/5000000000 : ℝ)|^5279 ≤ (3823565913379/10000000000000 : ℝ)^4255
        have hw : |(2303720119/5000000000 : ℝ)|=(2303720119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_4 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-355784793/2500000000 : ℝ)*x 0 + (5141602893/10000000000 : ℝ)*x 1 + (2734104619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (355784793/2500000000 : ℝ)^5279 ≤ (2225407492651/25000000000000 : ℝ)^4255 := by
    have hnat : (355784793 : ℕ)^5279*25000000000000^4255 ≤ 2225407492651^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355784793 2500000000 2225407492651 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141602893/10000000000 : ℝ)^5279 ≤ (21904940188801/50000000000000 : ℝ)^4255 := by
    have hnat : (5141602893 : ℕ)^5279*50000000000000^4255 ≤ 21904940188801^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141602893 10000000000 21904940188801 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734104619/5000000000 : ℝ)^5279 ≤ (47288489644229/100000000000000 : ℝ)^4255 := by
    have hnat : (2734104619 : ℕ)^5279*100000000000000^4255 ≤ 47288489644229^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734104619 5000000000 47288489644229 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-355784793/2500000000 : ℝ), (5141602893/10000000000 : ℝ), (2734104619/5000000000 : ℝ)] ![(2225407492651/25000000000000 : ℝ), (21904940188801/50000000000000 : ℝ), (47288489644229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-355784793/2500000000 : ℝ)|^5279 ≤ (2225407492651/25000000000000 : ℝ)^4255
        have hw : |(-355784793/2500000000 : ℝ)|=(355784793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141602893/10000000000 : ℝ)|^5279 ≤ (21904940188801/50000000000000 : ℝ)^4255
        have hw : |(5141602893/10000000000 : ℝ)|=(5141602893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734104619/5000000000 : ℝ)|^5279 ≤ (47288489644229/100000000000000 : ℝ)^4255
        have hw : |(2734104619/5000000000 : ℝ)|=(2734104619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_5 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313779869/2500000000 : ℝ)*x 0 + (-1265943851/10000000000 : ℝ)*x 1 + (5468209247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313779869/2500000000 : ℝ)^5279 ≤ (45013060933503/100000000000000 : ℝ)^4255 := by
    have hnat : (1313779869 : ℕ)^5279*100000000000000^4255 ≤ 45013060933503^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313779869 2500000000 45013060933503 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265943851/10000000000 : ℝ)^5279 ≤ (7698449309807/100000000000000 : ℝ)^4255 := by
    have hnat : (1265943851 : ℕ)^5279*100000000000000^4255 ≤ 7698449309807^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265943851 10000000000 7698449309807 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468209247/10000000000 : ℝ)^5279 ≤ (4728848974079/10000000000000 : ℝ)^4255 := by
    have hnat : (5468209247 : ℕ)^5279*10000000000000^4255 ≤ 4728848974079^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468209247 10000000000 4728848974079 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313779869/2500000000 : ℝ), (-1265943851/10000000000 : ℝ), (5468209247/10000000000 : ℝ)] ![(45013060933503/100000000000000 : ℝ), (7698449309807/100000000000000 : ℝ), (4728848974079/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313779869/2500000000 : ℝ)|^5279 ≤ (45013060933503/100000000000000 : ℝ)^4255
        have hw : |(1313779869/2500000000 : ℝ)|=(1313779869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1265943851/10000000000 : ℝ)|^5279 ≤ (7698449309807/100000000000000 : ℝ)^4255
        have hw : |(-1265943851/10000000000 : ℝ)|=(1265943851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468209247/10000000000 : ℝ)|^5279 ≤ (4728848974079/10000000000000 : ℝ)^4255
        have hw : |(5468209247/10000000000 : ℝ)|=(5468209247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_6 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313779891/2500000000 : ℝ)*x 0 + (1367052293/2500000000 : ℝ)*x 1 + (-632971917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313779891/2500000000 : ℝ)^5279 ≤ (45013061868673/100000000000000 : ℝ)^4255 := by
    have hnat : (1313779891 : ℕ)^5279*100000000000000^4255 ≤ 45013061868673^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313779891 2500000000 45013061868673 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367052293/2500000000 : ℝ)^5279 ≤ (4728848893611/10000000000000 : ℝ)^4255 := by
    have hnat : (1367052293 : ℕ)^5279*10000000000000^4255 ≤ 4728848893611^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367052293 2500000000 4728848893611 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632971917/5000000000 : ℝ)^5279 ≤ (7698449181547/100000000000000 : ℝ)^4255 := by
    have hnat : (632971917 : ℕ)^5279*100000000000000^4255 ≤ 7698449181547^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632971917 5000000000 7698449181547 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313779891/2500000000 : ℝ), (1367052293/2500000000 : ℝ), (-632971917/5000000000 : ℝ)] ![(45013061868673/100000000000000 : ℝ), (4728848893611/10000000000000 : ℝ), (7698449181547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313779891/2500000000 : ℝ)|^5279 ≤ (45013061868673/100000000000000 : ℝ)^4255
        have hw : |(1313779891/2500000000 : ℝ)|=(1313779891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367052293/2500000000 : ℝ)|^5279 ≤ (4728848893611/10000000000000 : ℝ)^4255
        have hw : |(1367052293/2500000000 : ℝ)|=(1367052293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-632971917/5000000000 : ℝ)|^5279 ≤ (7698449181547/100000000000000 : ℝ)^4255
        have hw : |(-632971917/5000000000 : ℝ)|=(632971917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_s3_7 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4109015029/10000000000 : ℝ)*x 0 + (2298408267/5000000000 : ℝ)*x 1 + (914096733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109015029/10000000000 : ℝ)^5279 ≤ (33172683506559/100000000000000 : ℝ)^4255 := by
    have hnat : (4109015029 : ℕ)^5279*100000000000000^4255 ≤ 33172683506559^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109015029 10000000000 33172683506559 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2298408267/5000000000 : ℝ)^5279 ≤ (38126309748203/100000000000000 : ℝ)^4255 := by
    have hnat : (2298408267 : ℕ)^5279*100000000000000^4255 ≤ 38126309748203^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2298408267 5000000000 38126309748203 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914096733/2500000000 : ℝ)^5279 ≤ (5740201344267/20000000000000 : ℝ)^4255 := by
    have hnat : (914096733 : ℕ)^5279*20000000000000^4255 ≤ 5740201344267^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914096733 2500000000 5740201344267 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109015029/10000000000 : ℝ), (2298408267/5000000000 : ℝ), (914096733/2500000000 : ℝ)] ![(33172683506559/100000000000000 : ℝ), (38126309748203/100000000000000 : ℝ), (5740201344267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109015029/10000000000 : ℝ)|^5279 ≤ (33172683506559/100000000000000 : ℝ)^4255
        have hw : |(4109015029/10000000000 : ℝ)|=(4109015029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2298408267/5000000000 : ℝ)|^5279 ≤ (38126309748203/100000000000000 : ℝ)^4255
        have hw : |(2298408267/5000000000 : ℝ)|=(2298408267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914096733/2500000000 : ℝ)|^5279 ≤ (5740201344267/20000000000000 : ℝ)^4255
        have hw : |(914096733/2500000000 : ℝ)|=(914096733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1707_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (4993/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8557/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (399/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17127/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (399/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (399/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17127/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (399/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (399/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17127/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (399/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (399/4000 : ℝ) ^ (5271/1024 : ℝ) ≤ (70298050303343/10000000000000000000 : ℝ) := by
    have hpowers : (399/4000 : ℝ)^5271 ≤ (70298050303343/10000000000000000000 : ℝ)^1024 := by
      have hnat : (399 : ℕ)^5271*10000000000000000000^1024 ≤ 70298050303343^1024*4000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        399 4000 70298050303343 10000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (399/4000 : ℝ)) (X := (70298050303343/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17127/100000 : ℝ) ^ (5271/1024 : ℝ) ≤ (11360682282969419/100000000000000000000 : ℝ) := by
    have hpowers : (17127/100000 : ℝ)^5271 ≤ (11360682282969419/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17127 : ℕ)^5271*100000000000000000000^1024 ≤ 11360682282969419^1024*100000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17127 100000 11360682282969419 100000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17127/100000 : ℝ)) (X := (11360682282969419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000070298050303343/5000000000000000000 : ℝ) ≤ (2000005462705049/2000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (5000070298050303343/5000000000000000000 : ℝ)^1024 ≤ (2000005462705049/2000000000000000 : ℝ)^5271 := by
      have hnat : (5000070298050303343 : ℕ)^1024*2000000000000000^5271 ≤ 2000005462705049^5271*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000070298050303343 5000000000000000000 2000005462705049 2000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005462705049/2000000000000000 : ℝ)) (X := (5000070298050303343/5000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012063662786002849/100000000000000000000 : ℝ) ≤ (10000234350035447/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (100012063662786002849/100000000000000000000 : ℝ)^1024 ≤ (10000234350035447/10000000000000000 : ℝ)^5271 := by
      have hnat : (100012063662786002849 : ℕ)^1024*10000000000000000^5271 ≤ 10000234350035447^5271*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012063662786002849 100000000000000000000 10000234350035447 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000234350035447/10000000000000000 : ℝ)) (X := (100012063662786002849/100000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50011360682282969419/50000000000000000000 : ℝ) ≤ (10000441386545649/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (50011360682282969419/50000000000000000000 : ℝ)^1024 ≤ (10000441386545649/10000000000000000 : ℝ)^5271 := by
      have hnat : (50011360682282969419 : ℕ)^1024*10000000000000000^5271 ≤ 10000441386545649^5271*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011360682282969419 50000000000000000000 10000441386545649 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000441386545649/10000000000000000 : ℝ)) (X := (50011360682282969419/50000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(70298050303343/10000000000000000000 : ℝ) ≤ ((1191934416132567039/1192000000000000000 : ℝ)+2*(103518255101/357600000000000 : ℝ)*(399/4000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (1191934416132567039/1192000000000000000 : ℝ)+2*(103518255101/357600000000000 : ℝ)*(399/4000 : ℝ)=(2000005462705049/2000000000000000 : ℝ) by norm_num, show 1+2*(70298050303343/10000000000000000000 : ℝ)=(5000070298050303343/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11360682282969419/100000000000000000000 : ℝ)+(70298050303343/10000000000000000000 : ℝ) ≤ ((1191934416132567039/1192000000000000000 : ℝ)+(103518255101/357600000000000 : ℝ)*((17127/100000 : ℝ)+(399/4000 : ℝ)))^(5271/1024 : ℝ) := by
    rw [show (1191934416132567039/1192000000000000000 : ℝ)+(103518255101/357600000000000 : ℝ)*((17127/100000 : ℝ)+(399/4000 : ℝ))=(10000234350035447/10000000000000000 : ℝ) by norm_num, show 1+(11360682282969419/100000000000000000000 : ℝ)+(70298050303343/10000000000000000000 : ℝ)=(100012063662786002849/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11360682282969419/100000000000000000000 : ℝ) ≤ ((1191934416132567039/1192000000000000000 : ℝ)+2*(103518255101/357600000000000 : ℝ)*(17127/100000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (1191934416132567039/1192000000000000000 : ℝ)+2*(103518255101/357600000000000 : ℝ)*(17127/100000 : ℝ)=(10000441386545649/10000000000000000 : ℝ) by norm_num, show 1+2*(11360682282969419/100000000000000000000 : ℝ)=(50011360682282969419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1191934416132567039/1192000000000000000 : ℝ)*(X 1 0+X 2 0)+(103518255101/357600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (399/4000 : ℝ)) (hi := (17127/100000 : ℝ)) (c := (1191934416132567039/1192000000000000000 : ℝ)) (alpha := (103518255101/357600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1191934416132567039/1192000000000000000 : ℝ)*(X 0 1+X 2 1)+(103518255101/357600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (399/4000 : ℝ)) (hi := (17127/100000 : ℝ)) (c := (1191934416132567039/1192000000000000000 : ℝ)) (alpha := (103518255101/357600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1191934416132567039/1192000000000000000 : ℝ)*(X 0 2+X 1 2)+(103518255101/357600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (399/4000 : ℝ)) (hi := (17127/100000 : ℝ)) (c := (1191934416132567039/1192000000000000000 : ℝ)) (alpha := (103518255101/357600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1422987453/10000000000 : ℝ)*X 0 0+(5471953887/10000000000 : ℝ)*X 0 1+(321119567/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344525031/10000000000 : ℝ)*X 1 0+(-1596239863/10000000000 : ℝ)*X 1 1+(5137913239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344525289/10000000000 : ℝ)*X 2 0+(2568956623/5000000000 : ℝ)*X 2 1+(-1596239509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4108577507/10000000000 : ℝ)*X 0 0+(3645604647/10000000000 : ℝ)*X 0 1+(2303720119/5000000000 : ℝ)*X 0 2+(4108577507/10000000000 : ℝ)*X 1 0+(3645604647/10000000000 : ℝ)*X 1 1+(2303720119/5000000000 : ℝ)*X 1 2+(4108577507/10000000000 : ℝ)*X 2 0+(3645604647/10000000000 : ℝ)*X 2 1+(2303720119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-355784793/2500000000 : ℝ)*X 0 0+(5141602893/10000000000 : ℝ)*X 0 1+(2734104619/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313779869/2500000000 : ℝ)*X 1 0+(-1265943851/10000000000 : ℝ)*X 1 1+(5468209247/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1313779891/2500000000 : ℝ)*X 2 0+(1367052293/2500000000 : ℝ)*X 2 1+(-632971917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4109015029/10000000000 : ℝ)*X 0 0+(2298408267/5000000000 : ℝ)*X 0 1+(914096733/2500000000 : ℝ)*X 0 2+(4109015029/10000000000 : ℝ)*X 1 0+(2298408267/5000000000 : ℝ)*X 1 1+(914096733/2500000000 : ℝ)*X 1 2+(4109015029/10000000000 : ℝ)*X 2 0+(2298408267/5000000000 : ℝ)*X 2 1+(914096733/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (357770496706978282443977577/59600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (554937521/50000000000000 : ℝ)*(base19) + (1186621147/100000000000000 : ℝ)*(base23) + (15768797/20000000000000 : ℝ)*(upper3) + (36219559/100000000000000 : ℝ)*(upper4) + (138272029/50000000000000 : ℝ)*(upper5) + (2016679415303619/100000000000000 : ℝ)*(major0) + (2016679415303619/100000000000000 : ℝ)*(major1) + (2016679415303619/100000000000000 : ℝ)*(major2) + (2993656532219477/100000000000000 : ℝ)*(sp0) + (748417721671041/25000000000000 : ℝ)*(sp1) + (1496835404969029/50000000000000 : ℝ)*(sp2) + (259920763070611/25000000000000 : ℝ)*(sp3) + (15464339729/100000000000000 : ℝ)*(sp4) + (3581670227/100000000000000 : ℝ)*(sp7) + (1039686633952671/100000000000000 : ℝ)*(f.failure) + (1496835998279603/50000000000000 : ℝ)*(f.sum) + (23805226527053/5960000000000000000000000000 : ℝ)*base65 + (1112361137215855859/119200000000000000000000000000000 : ℝ)*base68 + (378183427984144141/119200000000000000000000000000000 : ℝ)*base69 + (17210445021455859/119200000000000000000000000000000 : ℝ)*base72 + (32929078715667/5960000000000000000000000000 : ℝ)*base74 + (463086327864144141/119200000000000000000000000000000 : ℝ)*base75 + (648492985360944141/119200000000000000000000000000000 : ℝ)*base77 + (107147460681744141/119200000000000000000000000000000 : ℝ)*base79 + (10006160754733/5960000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6159711/1250000000000000000000 : ℝ)*base89 + (6159711/1250000000000000000000 : ℝ)*base91 + (6159711/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (240667849821997939230506113/59600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101409961/20000000000000 : ℝ)*(base19) + (304438261/50000000000000 : ℝ)*(base23) + (31262939/20000000000000 : ℝ)*(lower1) + (38112633/50000000000000 : ℝ)*(upper3) + (11760089/50000000000000 : ℝ)*(lower4) + (12004337/12500000000000 : ℝ)*(upper5) + (2062563739204811/100000000000000 : ℝ)*(major0) + (2062563739204811/100000000000000 : ℝ)*(major1) + (2062563739204811/100000000000000 : ℝ)*(major2) + (68167011/20000000000000 : ℝ)*(sp2) + (765446332419073/25000000000000 : ℝ)*(sp4) + (1530892411313243/50000000000000 : ℝ)*(sp5) + (1530892189982357/50000000000000 : ℝ)*(sp6) + (531671007065799/50000000000000 : ℝ)*(sp7) + (531671007065799/50000000000000 : ℝ)*(f.failure) + (765446332419073/25000000000000 : ℝ)*(f.sum) + (70485119501071/17880000000000000000000000000 : ℝ)*base65 + (3236625761066783887/357600000000000000000000000000000 : ℝ)*base67 + (1994141434212383887/357600000000000000000000000000000 : ℝ)*base69 + (42149813754717216113/357600000000000000000000000000000 : ℝ)*base72 + (7756466487569/17880000000000000000000000000 : ℝ)*base74 + (23076597569037216113/357600000000000000000000000000000 : ℝ)*base76 + (1854929863694783887/357600000000000000000000000000000 : ℝ)*base77 + (1728954629743583887/357600000000000000000000000000000 : ℝ)*base79 + (83974868824711/17880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3338441/625000000000000000000 : ℝ)*base90 + (3338441/625000000000000000000 : ℝ)*base92 + (3338441/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1707_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8557/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1707_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1707_box_0 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-551013823/5000000000 : ℝ)*x 0 + (677352409/1250000000 : ℝ)*x 1 + (1354704623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551013823/5000000000 : ℝ)^5279 ≤ (6481692183217/100000000000000 : ℝ)^4255 := by
    have hnat : (551013823 : ℕ)^5279*100000000000000^4255 ≤ 6481692183217^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551013823 5000000000 6481692183217 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677352409/1250000000 : ℝ)^5279 ≤ (730611844929/1562500000000 : ℝ)^4255 := by
    have hnat : (677352409 : ℕ)^5279*1562500000000^4255 ≤ 730611844929^4255*1250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677352409 1250000000 730611844929 1562500000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354704623/2500000000 : ℝ)^5279 ≤ (46759149725029/100000000000000 : ℝ)^4255 := by
    have hnat : (1354704623 : ℕ)^5279*100000000000000^4255 ≤ 46759149725029^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354704623 2500000000 46759149725029 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-551013823/5000000000 : ℝ), (677352409/1250000000 : ℝ), (1354704623/2500000000 : ℝ)] ![(6481692183217/100000000000000 : ℝ), (730611844929/1562500000000 : ℝ), (46759149725029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-551013823/5000000000 : ℝ)|^5279 ≤ (6481692183217/100000000000000 : ℝ)^4255
        have hw : |(-551013823/5000000000 : ℝ)|=(551013823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677352409/1250000000 : ℝ)|^5279 ≤ (730611844929/1562500000000 : ℝ)^4255
        have hw : |(677352409/1250000000 : ℝ)|=(677352409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354704623/2500000000 : ℝ)|^5279 ≤ (46759149725029/100000000000000 : ℝ)^4255
        have hw : |(1354704623/2500000000 : ℝ)|=(1354704623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_1 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612770323/5000000000 : ℝ)*x 0 + (-344149753/2500000000 : ℝ)*x 1 + (2709409593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612770323/5000000000 : ℝ)^5279 ≤ (2793683862909/6250000000000 : ℝ)^4255 := by
    have hnat : (2612770323 : ℕ)^5279*6250000000000^4255 ≤ 2793683862909^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612770323 5000000000 2793683862909 6250000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344149753/2500000000 : ℝ)^5279 ≤ (8541901029249/100000000000000 : ℝ)^4255 := by
    have hnat : (344149753 : ℕ)^5279*100000000000000^4255 ≤ 8541901029249^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344149753 2500000000 8541901029249 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709409593/5000000000 : ℝ)^5279 ≤ (2922447322173/6250000000000 : ℝ)^4255 := by
    have hnat : (2709409593 : ℕ)^5279*6250000000000^4255 ≤ 2922447322173^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709409593 5000000000 2922447322173 6250000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612770323/5000000000 : ℝ), (-344149753/2500000000 : ℝ), (2709409593/5000000000 : ℝ)] ![(2793683862909/6250000000000 : ℝ), (8541901029249/100000000000000 : ℝ), (2922447322173/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612770323/5000000000 : ℝ)|^5279 ≤ (2793683862909/6250000000000 : ℝ)^4255
        have hw : |(2612770323/5000000000 : ℝ)|=(2612770323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344149753/2500000000 : ℝ)|^5279 ≤ (8541901029249/100000000000000 : ℝ)^4255
        have hw : |(-344149753/2500000000 : ℝ)|=(344149753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709409593/5000000000 : ℝ)|^5279 ≤ (2922447322173/6250000000000 : ℝ)^4255
        have hw : |(2709409593/5000000000 : ℝ)|=(2709409593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_2 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612770607/5000000000 : ℝ)*x 0 + (2709409289/5000000000 : ℝ)*x 1 + (-688299537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612770607/5000000000 : ℝ)^5279 ≤ (44698947834449/100000000000000 : ℝ)^4255 := by
    have hnat : (2612770607 : ℕ)^5279*100000000000000^4255 ≤ 44698947834449^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612770607 5000000000 44698947834449 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709409289/5000000000 : ℝ)^5279 ≤ (46759150645717/100000000000000 : ℝ)^4255 := by
    have hnat : (2709409289 : ℕ)^5279*100000000000000^4255 ≤ 46759150645717^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709409289 5000000000 46759150645717 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688299537/5000000000 : ℝ)^5279 ≤ (2135475376637/25000000000000 : ℝ)^4255 := by
    have hnat : (688299537 : ℕ)^5279*25000000000000^4255 ≤ 2135475376637^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688299537 5000000000 2135475376637 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612770607/5000000000 : ℝ), (2709409289/5000000000 : ℝ), (-688299537/5000000000 : ℝ)] ![(44698947834449/100000000000000 : ℝ), (46759150645717/100000000000000 : ℝ), (2135475376637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612770607/5000000000 : ℝ)|^5279 ≤ (44698947834449/100000000000000 : ℝ)^4255
        have hw : |(2612770607/5000000000 : ℝ)|=(2612770607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709409289/5000000000 : ℝ)|^5279 ≤ (46759150645717/100000000000000 : ℝ)^4255
        have hw : |(2709409289/5000000000 : ℝ)|=(2709409289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-688299537/5000000000 : ℝ)|^5279 ≤ (2135475376637/25000000000000 : ℝ)^4255
        have hw : |(-688299537/5000000000 : ℝ)|=(688299537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_3 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4490766791/10000000000 : ℝ)*x 0 + (984814923/2500000000 : ℝ)*x 1 + (3939259503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490766791/10000000000 : ℝ)^5279 ≤ (37038094268327/100000000000000 : ℝ)^4255 := by
    have hnat : (4490766791 : ℕ)^5279*100000000000000^4255 ≤ 37038094268327^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490766791 10000000000 37038094268327 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984814923/2500000000 : ℝ)^5279 ≤ (3148095379877/10000000000000 : ℝ)^4255 := by
    have hnat : (984814923 : ℕ)^5279*10000000000000^4255 ≤ 3148095379877^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984814923 2500000000 3148095379877 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3939259503/10000000000 : ℝ)^5279 ≤ (31480951924867/100000000000000 : ℝ)^4255 := by
    have hnat : (3939259503 : ℕ)^5279*100000000000000^4255 ≤ 31480951924867^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3939259503 10000000000 31480951924867 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490766791/10000000000 : ℝ), (984814923/2500000000 : ℝ), (3939259503/10000000000 : ℝ)] ![(37038094268327/100000000000000 : ℝ), (3148095379877/10000000000000 : ℝ), (31480951924867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490766791/10000000000 : ℝ)|^5279 ≤ (37038094268327/100000000000000 : ℝ)^4255
        have hw : |(4490766791/10000000000 : ℝ)|=(4490766791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984814923/2500000000 : ℝ)|^5279 ≤ (3148095379877/10000000000000 : ℝ)^4255
        have hw : |(984814923/2500000000 : ℝ)|=(984814923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3939259503/10000000000 : ℝ)|^5279 ≤ (31480951924867/100000000000000 : ℝ)^4255
        have hw : |(3939259503/10000000000 : ℝ)|=(3939259503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_4 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-352927689/2000000000 : ℝ)*x 0 + (1294334867/2500000000 : ℝ)*x 1 + (5177339623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352927689/2000000000 : ℝ)^5279 ≤ (2906011873657/25000000000000 : ℝ)^4255 := by
    have hnat : (352927689 : ℕ)^5279*25000000000000^4255 ≤ 2906011873657^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352927689 2000000000 2906011873657 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294334867/2500000000 : ℝ)^5279 ≤ (8837595085599/20000000000000 : ℝ)^4255 := by
    have hnat : (1294334867 : ℕ)^5279*20000000000000^4255 ≤ 8837595085599^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294334867 2500000000 8837595085599 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177339623/10000000000 : ℝ)^5279 ≤ (4418797706927/10000000000000 : ℝ)^4255 := by
    have hnat : (5177339623 : ℕ)^5279*10000000000000^4255 ≤ 4418797706927^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177339623 10000000000 4418797706927 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352927689/2000000000 : ℝ), (1294334867/2500000000 : ℝ), (5177339623/10000000000 : ℝ)] ![(2906011873657/25000000000000 : ℝ), (8837595085599/20000000000000 : ℝ), (4418797706927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352927689/2000000000 : ℝ)|^5279 ≤ (2906011873657/25000000000000 : ℝ)^4255
        have hw : |(-352927689/2000000000 : ℝ)|=(352927689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294334867/2500000000 : ℝ)|^5279 ≤ (8837595085599/20000000000000 : ℝ)^4255
        have hw : |(1294334867/2500000000 : ℝ)|=(1294334867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177339623/10000000000 : ℝ)|^5279 ≤ (4418797706927/10000000000000 : ℝ)^4255
        have hw : |(5177339623/10000000000 : ℝ)|=(5177339623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_5 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389424269/10000000000 : ℝ)*x 0 + (-185356771/1250000000 : ℝ)*x 1 + (2588670071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389424269/10000000000 : ℝ)^5279 ≤ (46444670379411/100000000000000 : ℝ)^4255 := by
    have hnat : (5389424269 : ℕ)^5279*100000000000000^4255 ≤ 46444670379411^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389424269 10000000000 46444670379411 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185356771/1250000000 : ℝ)^5279 ≤ (2341836760161/25000000000000 : ℝ)^4255 := by
    have hnat : (185356771 : ℕ)^5279*25000000000000^4255 ≤ 2341836760161^4255*1250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185356771 1250000000 2341836760161 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588670071/5000000000 : ℝ)^5279 ≤ (44187982564893/100000000000000 : ℝ)^4255 := by
    have hnat : (2588670071 : ℕ)^5279*100000000000000^4255 ≤ 44187982564893^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588670071 5000000000 44187982564893 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389424269/10000000000 : ℝ), (-185356771/1250000000 : ℝ), (2588670071/5000000000 : ℝ)] ![(46444670379411/100000000000000 : ℝ), (2341836760161/25000000000000 : ℝ), (44187982564893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389424269/10000000000 : ℝ)|^5279 ≤ (46444670379411/100000000000000 : ℝ)^4255
        have hw : |(5389424269/10000000000 : ℝ)|=(5389424269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185356771/1250000000 : ℝ)|^5279 ≤ (2341836760161/25000000000000 : ℝ)^4255
        have hw : |(-185356771/1250000000 : ℝ)|=(185356771/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588670071/5000000000 : ℝ)|^5279 ≤ (44187982564893/100000000000000 : ℝ)^4255
        have hw : |(2588670071/5000000000 : ℝ)|=(2588670071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_6 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077884867/2000000000 : ℝ)*x 0 + (5177340087/10000000000 : ℝ)*x 1 + (-1482854153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077884867/2000000000 : ℝ)^5279 ≤ (46444671085061/100000000000000 : ℝ)^4255 := by
    have hnat : (1077884867 : ℕ)^5279*100000000000000^4255 ≤ 46444671085061^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077884867 2000000000 46444671085061 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177340087/10000000000 : ℝ)^5279 ≤ (8837596396501/20000000000000 : ℝ)^4255 := by
    have hnat : (5177340087 : ℕ)^5279*20000000000000^4255 ≤ 8837596396501^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177340087 10000000000 8837596396501 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482854153/10000000000 : ℝ)^5279 ≤ (9367346923083/100000000000000 : ℝ)^4255 := by
    have hnat : (1482854153 : ℕ)^5279*100000000000000^4255 ≤ 9367346923083^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482854153 10000000000 9367346923083 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077884867/2000000000 : ℝ), (5177340087/10000000000 : ℝ), (-1482854153/10000000000 : ℝ)] ![(46444671085061/100000000000000 : ℝ), (8837596396501/20000000000000 : ℝ), (9367346923083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077884867/2000000000 : ℝ)|^5279 ≤ (46444671085061/100000000000000 : ℝ)^4255
        have hw : |(1077884867/2000000000 : ℝ)|=(1077884867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177340087/10000000000 : ℝ)|^5279 ≤ (8837596396501/20000000000000 : ℝ)^4255
        have hw : |(5177340087/10000000000 : ℝ)|=(5177340087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1482854153/10000000000 : ℝ)|^5279 ≤ (9367346923083/100000000000000 : ℝ)^4255
        have hw : |(-1482854153/10000000000 : ℝ)|=(1482854153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_7 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1855450837/5000000000 : ℝ)*x 0 + (4328360037/10000000000 : ℝ)*x 1 + (4328360291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1855450837/5000000000 : ℝ)^5279 ≤ (29232853543597/100000000000000 : ℝ)^4255 := by
    have hnat : (1855450837 : ℕ)^5279*100000000000000^4255 ≤ 29232853543597^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855450837 5000000000 29232853543597 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4328360037/10000000000 : ℝ)^5279 ≤ (35383571931401/100000000000000 : ℝ)^4255 := by
    have hnat : (4328360037 : ℕ)^5279*100000000000000^4255 ≤ 35383571931401^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328360037 10000000000 35383571931401 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4328360291/10000000000 : ℝ)^5279 ≤ (35383574507509/100000000000000 : ℝ)^4255 := by
    have hnat : (4328360291 : ℕ)^5279*100000000000000^4255 ≤ 35383574507509^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328360291 10000000000 35383574507509 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1855450837/5000000000 : ℝ), (4328360037/10000000000 : ℝ), (4328360291/10000000000 : ℝ)] ![(29232853543597/100000000000000 : ℝ), (35383571931401/100000000000000 : ℝ), (35383574507509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1855450837/5000000000 : ℝ)|^5279 ≤ (29232853543597/100000000000000 : ℝ)^4255
        have hw : |(1855450837/5000000000 : ℝ)|=(1855450837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4328360037/10000000000 : ℝ)|^5279 ≤ (35383571931401/100000000000000 : ℝ)^4255
        have hw : |(4328360037/10000000000 : ℝ)|=(4328360037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4328360291/10000000000 : ℝ)|^5279 ≤ (35383574507509/100000000000000 : ℝ)^4255
        have hw : |(4328360291/10000000000 : ℝ)|=(4328360291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_8 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-64886757/400000000 : ℝ)*x 0 + (399941/800000 : ℝ)*x 1 + (682710797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64886757/400000000 : ℝ)^5279 ≤ (10471269578401/100000000000000 : ℝ)^4255 := by
    have hnat : (64886757 : ℕ)^5279*100000000000000^4255 ≤ 10471269578401^4255*400000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64886757 400000000 10471269578401 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399941/800000 : ℝ)^5279 ≤ (42310215009303/100000000000000 : ℝ)^4255 := by
    have hnat : (399941 : ℕ)^5279*100000000000000^4255 ≤ 42310215009303^4255*800000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399941 800000 42310215009303 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682710797/1250000000 : ℝ)^5279 ≤ (47218515395161/100000000000000 : ℝ)^4255 := by
    have hnat : (682710797 : ℕ)^5279*100000000000000^4255 ≤ 47218515395161^4255*1250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682710797 1250000000 47218515395161 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64886757/400000000 : ℝ), (399941/800000 : ℝ), (682710797/1250000000 : ℝ)] ![(10471269578401/100000000000000 : ℝ), (42310215009303/100000000000000 : ℝ), (47218515395161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64886757/400000000 : ℝ)|^5279 ≤ (10471269578401/100000000000000 : ℝ)^4255
        have hw : |(-64886757/400000000 : ℝ)|=(64886757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(399941/800000 : ℝ)|^5279 ≤ (42310215009303/100000000000000 : ℝ)^4255
        have hw : |(399941/800000 : ℝ)|=(399941/800000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682710797/1250000000 : ℝ)|^5279 ≤ (47218515395161/100000000000000 : ℝ)^4255
        have hw : |(682710797/1250000000 : ℝ)|=(682710797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_9 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (51964661/100000000 : ℝ)*x 0 + (-339237133/2500000000 : ℝ)*x 1 + (682710853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51964661/100000000 : ℝ)^5279 ≤ (11097648691967/25000000000000 : ℝ)^4255 := by
    have hnat : (51964661 : ℕ)^5279*25000000000000^4255 ≤ 11097648691967^4255*100000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51964661 100000000 11097648691967 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339237133/2500000000 : ℝ)^5279 ≤ (8390885010839/100000000000000 : ℝ)^4255 := by
    have hnat : (339237133 : ℕ)^5279*100000000000000^4255 ≤ 8390885010839^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339237133 2500000000 8390885010839 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682710853/1250000000 : ℝ)^5279 ≤ (5902315025051/12500000000000 : ℝ)^4255 := by
    have hnat : (682710853 : ℕ)^5279*12500000000000^4255 ≤ 5902315025051^4255*1250000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682710853 1250000000 5902315025051 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51964661/100000000 : ℝ), (-339237133/2500000000 : ℝ), (682710853/1250000000 : ℝ)] ![(11097648691967/25000000000000 : ℝ), (8390885010839/100000000000000 : ℝ), (5902315025051/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51964661/100000000 : ℝ)|^5279 ≤ (11097648691967/25000000000000 : ℝ)^4255
        have hw : |(51964661/100000000 : ℝ)|=(51964661/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-339237133/2500000000 : ℝ)|^5279 ≤ (8390885010839/100000000000000 : ℝ)^4255
        have hw : |(-339237133/2500000000 : ℝ)|=(339237133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682710853/1250000000 : ℝ)|^5279 ≤ (5902315025051/12500000000000 : ℝ)^4255
        have hw : |(682710853/1250000000 : ℝ)|=(682710853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_10 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598233551/5000000000 : ℝ)*x 0 + (27308429/50000000 : ℝ)*x 1 + (-67847429/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598233551/5000000000 : ℝ)^5279 ≤ (22195302693667/50000000000000 : ℝ)^4255 := by
    have hnat : (2598233551 : ℕ)^5279*50000000000000^4255 ≤ 22195302693667^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598233551 5000000000 22195302693667 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27308429/50000000 : ℝ)^5279 ≤ (47218509216987/100000000000000 : ℝ)^4255 := by
    have hnat : (27308429 : ℕ)^5279*100000000000000^4255 ≤ 47218509216987^4255*50000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27308429 50000000 47218509216987 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67847429/500000000 : ℝ)^5279 ≤ (1678177075817/20000000000000 : ℝ)^4255 := by
    have hnat : (67847429 : ℕ)^5279*20000000000000^4255 ≤ 1678177075817^4255*500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67847429 500000000 1678177075817 20000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598233551/5000000000 : ℝ), (27308429/50000000 : ℝ), (-67847429/500000000 : ℝ)] ![(22195302693667/50000000000000 : ℝ), (47218509216987/100000000000000 : ℝ), (1678177075817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598233551/5000000000 : ℝ)|^5279 ≤ (22195302693667/50000000000000 : ℝ)^4255
        have hw : |(2598233551/5000000000 : ℝ)|=(2598233551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27308429/50000000 : ℝ)|^5279 ≤ (47218509216987/100000000000000 : ℝ)^4255
        have hw : |(27308429/50000000 : ℝ)|=(27308429/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67847429/500000000 : ℝ)|^5279 ≤ (1678177075817/20000000000000 : ℝ)^4255
        have hw : |(-67847429/500000000 : ℝ)|=(67847429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_11 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1156054677/2500000000 : ℝ)*x 0 + (1935001741/5000000000 : ℝ)*x 1 + (774001073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1156054677/2500000000 : ℝ)^5279 ≤ (4801060359797/12500000000000 : ℝ)^4255 := by
    have hnat : (1156054677 : ℕ)^5279*12500000000000^4255 ≤ 4801060359797^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156054677 2500000000 4801060359797 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1935001741/5000000000 : ℝ)^5279 ≤ (30795749256417/100000000000000 : ℝ)^4255 := by
    have hnat : (1935001741 : ℕ)^5279*100000000000000^4255 ≤ 30795749256417^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935001741 5000000000 30795749256417 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774001073/2000000000 : ℝ)^5279 ≤ (30795767846523/100000000000000 : ℝ)^4255 := by
    have hnat : (774001073 : ℕ)^5279*100000000000000^4255 ≤ 30795767846523^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774001073 2000000000 30795767846523 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1156054677/2500000000 : ℝ), (1935001741/5000000000 : ℝ), (774001073/2000000000 : ℝ)] ![(4801060359797/12500000000000 : ℝ), (30795749256417/100000000000000 : ℝ), (30795767846523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1156054677/2500000000 : ℝ)|^5279 ≤ (4801060359797/12500000000000 : ℝ)^4255
        have hw : |(1156054677/2500000000 : ℝ)|=(1156054677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1935001741/5000000000 : ℝ)|^5279 ≤ (30795749256417/100000000000000 : ℝ)^4255
        have hw : |(1935001741/5000000000 : ℝ)|=(1935001741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(774001073/2000000000 : ℝ)|^5279 ≤ (30795767846523/100000000000000 : ℝ)^4255
        have hw : |(774001073/2000000000 : ℝ)|=(774001073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_12 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1239130869/10000000000 : ℝ)*x 0 + (1117682333/2000000000 : ℝ)*x 1 + (2576092991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1239130869/10000000000 : ℝ)^5279 ≤ (7496672260969/100000000000000 : ℝ)^4255 := by
    have hnat : (1239130869 : ℕ)^5279*100000000000000^4255 ≤ 7496672260969^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239130869 10000000000 7496672260969 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117682333/2000000000 : ℝ)^5279 ≤ (48581543356751/100000000000000 : ℝ)^4255 := by
    have hnat : (1117682333 : ℕ)^5279*100000000000000^4255 ≤ 48581543356751^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117682333 2000000000 48581543356751 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576092991/5000000000 : ℝ)^5279 ≤ (5490223046123/12500000000000 : ℝ)^4255 := by
    have hnat : (2576092991 : ℕ)^5279*12500000000000^4255 ≤ 5490223046123^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576092991 5000000000 5490223046123 12500000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1239130869/10000000000 : ℝ), (1117682333/2000000000 : ℝ), (2576092991/5000000000 : ℝ)] ![(7496672260969/100000000000000 : ℝ), (48581543356751/100000000000000 : ℝ), (5490223046123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1239130869/10000000000 : ℝ)|^5279 ≤ (7496672260969/100000000000000 : ℝ)^4255
        have hw : |(-1239130869/10000000000 : ℝ)|=(1239130869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117682333/2000000000 : ℝ)|^5279 ≤ (48581543356751/100000000000000 : ℝ)^4255
        have hw : |(1117682333/2000000000 : ℝ)|=(1117682333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576092991/5000000000 : ℝ)|^5279 ≤ (5490223046123/12500000000000 : ℝ)^4255
        have hw : |(2576092991/5000000000 : ℝ)|=(2576092991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_13 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406526061/10000000000 : ℝ)*x 0 + (-746735721/5000000000 : ℝ)*x 1 + (5152185853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406526061/10000000000 : ℝ)^5279 ≤ (4662758688279/10000000000000 : ℝ)^4255 := by
    have hnat : (5406526061 : ℕ)^5279*10000000000000^4255 ≤ 4662758688279^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406526061 10000000000 4662758688279 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746735721/5000000000 : ℝ)^5279 ≤ (4725315045623/50000000000000 : ℝ)^4255 := by
    have hnat : (746735721 : ℕ)^5279*50000000000000^4255 ≤ 4725315045623^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746735721 5000000000 4725315045623 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152185853/10000000000 : ℝ)^5279 ≤ (2196089150231/5000000000000 : ℝ)^4255 := by
    have hnat : (5152185853 : ℕ)^5279*5000000000000^4255 ≤ 2196089150231^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152185853 10000000000 2196089150231 5000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406526061/10000000000 : ℝ), (-746735721/5000000000 : ℝ), (5152185853/10000000000 : ℝ)] ![(4662758688279/10000000000000 : ℝ), (4725315045623/50000000000000 : ℝ), (2196089150231/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406526061/10000000000 : ℝ)|^5279 ≤ (4662758688279/10000000000000 : ℝ)^4255
        have hw : |(5406526061/10000000000 : ℝ)|=(5406526061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-746735721/5000000000 : ℝ)|^5279 ≤ (4725315045623/50000000000000 : ℝ)^4255
        have hw : |(-746735721/5000000000 : ℝ)|=(746735721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152185853/10000000000 : ℝ)|^5279 ≤ (2196089150231/5000000000000 : ℝ)^4255
        have hw : |(5152185853/10000000000 : ℝ)|=(5152185853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_14 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351631533/2500000000 : ℝ)*x 0 + (2576092851/5000000000 : ℝ)*x 1 + (-29869431/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351631533/2500000000 : ℝ)^5279 ≤ (23313793821239/50000000000000 : ℝ)^4255 := by
    have hnat : (1351631533 : ℕ)^5279*50000000000000^4255 ≤ 23313793821239^4255*2500000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351631533 2500000000 23313793821239 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576092851/5000000000 : ℝ)^5279 ≤ (21960890703787/50000000000000 : ℝ)^4255 := by
    have hnat : (2576092851 : ℕ)^5279*50000000000000^4255 ≤ 21960890703787^4255*5000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576092851 5000000000 21960890703787 50000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29869431/200000000 : ℝ)^5279 ≤ (18458263553/195312500000 : ℝ)^4255 := by
    have hnat : (29869431 : ℕ)^5279*195312500000^4255 ≤ 18458263553^4255*200000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29869431 200000000 18458263553 195312500000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351631533/2500000000 : ℝ), (2576092851/5000000000 : ℝ), (-29869431/200000000 : ℝ)] ![(23313793821239/50000000000000 : ℝ), (21960890703787/50000000000000 : ℝ), (18458263553/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351631533/2500000000 : ℝ)|^5279 ≤ (23313793821239/50000000000000 : ℝ)^4255
        have hw : |(1351631533/2500000000 : ℝ)|=(1351631533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576092851/5000000000 : ℝ)|^5279 ≤ (21960890703787/50000000000000 : ℝ)^4255
        have hw : |(2576092851/5000000000 : ℝ)|=(2576092851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29869431/200000000 : ℝ)|^5279 ≤ (18458263553/195312500000 : ℝ)^4255
        have hw : |(-29869431/200000000 : ℝ)|=(29869431/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1707_box_15 (p : ℝ) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3626682121/10000000000 : ℝ)*x 0 + (873756431/2000000000 : ℝ)*x 1 + (43687817/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3626682121/10000000000 : ℝ)^5279 ≤ (7103001614547/25000000000000 : ℝ)^4255 := by
    have hnat : (3626682121 : ℕ)^5279*25000000000000^4255 ≤ 7103001614547^4255*10000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3626682121 10000000000 7103001614547 25000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873756431/2000000000 : ℝ)^5279 ≤ (3579399906973/10000000000000 : ℝ)^4255 := by
    have hnat : (873756431 : ℕ)^5279*10000000000000^4255 ≤ 3579399906973^4255*2000000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873756431 2000000000 3579399906973 10000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43687817/100000000 : ℝ)^5279 ≤ (35793994444713/100000000000000 : ℝ)^4255 := by
    have hnat : (43687817 : ℕ)^5279*100000000000000^4255 ≤ 35793994444713^4255*100000000^5279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43687817 100000000 35793994444713 100000000000000 5279 4255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5279/1024 : ℝ)) 5279 4255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3626682121/10000000000 : ℝ), (873756431/2000000000 : ℝ), (43687817/100000000 : ℝ)] ![(7103001614547/25000000000000 : ℝ), (3579399906973/10000000000000 : ℝ), (35793994444713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3626682121/10000000000 : ℝ)|^5279 ≤ (7103001614547/25000000000000 : ℝ)^4255
        have hw : |(3626682121/10000000000 : ℝ)|=(3626682121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873756431/2000000000 : ℝ)|^5279 ≤ (3579399906973/10000000000000 : ℝ)^4255
        have hw : |(873756431/2000000000 : ℝ)|=(873756431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43687817/100000000 : ℝ)|^5279 ≤ (35793994444713/100000000000000 : ℝ)^4255
        have hw : |(43687817/100000000 : ℝ)|=(43687817/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1707_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8557/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66719/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14583/25000 : ℝ) ∧ (10173/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4519/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8557/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4993/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8557/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4993/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8557/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4993/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8557/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4993/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8557/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4993/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8557/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4993/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4993/50000 : ℝ) ^ (5271/1024 : ℝ) ≤ (44186252253721/6250000000000000000 : ℝ) := by
    have hpowers : (4993/50000 : ℝ)^5271 ≤ (44186252253721/6250000000000000000 : ℝ)^1024 := by
      have hnat : (4993 : ℕ)^5271*6250000000000000000^1024 ≤ 44186252253721^1024*50000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4993 50000 44186252253721 6250000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4993/50000 : ℝ)) (X := (44186252253721/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8557/50000 : ℝ) ^ (5271/1024 : ℝ) ≤ (2829091178218159/25000000000000000000 : ℝ) := by
    have hpowers : (8557/50000 : ℝ)^5271 ≤ (2829091178218159/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8557 : ℕ)^5271*25000000000000000000^1024 ≤ 2829091178218159^1024*50000^5271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8557 50000 2829091178218159 25000000000000000000 5271 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8557/50000 : ℝ)) (X := (2829091178218159/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125044186252253721/3125000000000000000 : ℝ) ≤ (2000005493784353/2000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (3125044186252253721/3125000000000000000 : ℝ)^1024 ≤ (2000005493784353/2000000000000000 : ℝ)^5271 := by
      have hnat : (3125044186252253721 : ℕ)^1024*2000000000000000^5271 ≤ 2000005493784353^5271*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125044186252253721 3125000000000000000 2000005493784353 2000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005493784353/2000000000000000 : ℝ)) (X := (3125044186252253721/3125000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003005836187233043/25000000000000000000 : ℝ) ≤ (5000116783425387/5000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (25003005836187233043/25000000000000000000 : ℝ)^1024 ≤ (5000116783425387/5000000000000000 : ℝ)^5271 := by
      have hnat : (25003005836187233043 : ℕ)^1024*5000000000000000^5271 ≤ 5000116783425387^5271*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003005836187233043 25000000000000000000 5000116783425387 5000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000116783425387/5000000000000000 : ℝ)) (X := (25003005836187233043/25000000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502829091178218159/12500000000000000000 : ℝ) ≤ (10000439664779783/10000000000000000 : ℝ) ^ (5271/1024 : ℝ) := by
    have hpowers : (12502829091178218159/12500000000000000000 : ℝ)^1024 ≤ (10000439664779783/10000000000000000 : ℝ)^5271 := by
      have hnat : (12502829091178218159 : ℕ)^1024*10000000000000000^5271 ≤ 10000439664779783^5271*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502829091178218159 12500000000000000000 10000439664779783 10000000000000000 1024 5271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000439664779783/10000000000000000 : ℝ)) (X := (12502829091178218159/12500000000000000000 : ℝ)) (by norm_num) 5271 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(44186252253721/6250000000000000000 : ℝ) ≤ ((17819019902659043293/17820000000000000000 : ℝ)+2*(206097929009/712800000000000 : ℝ)*(4993/50000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (17819019902659043293/17820000000000000000 : ℝ)+2*(206097929009/712800000000000 : ℝ)*(4993/50000 : ℝ)=(2000005493784353/2000000000000000 : ℝ) by norm_num, show 1+2*(44186252253721/6250000000000000000 : ℝ)=(3125044186252253721/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2829091178218159/25000000000000000000 : ℝ)+(44186252253721/6250000000000000000 : ℝ) ≤ ((17819019902659043293/17820000000000000000 : ℝ)+(206097929009/712800000000000 : ℝ)*((8557/50000 : ℝ)+(4993/50000 : ℝ)))^(5271/1024 : ℝ) := by
    rw [show (17819019902659043293/17820000000000000000 : ℝ)+(206097929009/712800000000000 : ℝ)*((8557/50000 : ℝ)+(4993/50000 : ℝ))=(5000116783425387/5000000000000000 : ℝ) by norm_num, show 1+(2829091178218159/25000000000000000000 : ℝ)+(44186252253721/6250000000000000000 : ℝ)=(25003005836187233043/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2829091178218159/25000000000000000000 : ℝ) ≤ ((17819019902659043293/17820000000000000000 : ℝ)+2*(206097929009/712800000000000 : ℝ)*(8557/50000 : ℝ))^(5271/1024 : ℝ) := by
    rw [show (17819019902659043293/17820000000000000000 : ℝ)+2*(206097929009/712800000000000 : ℝ)*(8557/50000 : ℝ)=(10000439664779783/10000000000000000 : ℝ) by norm_num, show 1+2*(2829091178218159/25000000000000000000 : ℝ)=(12502829091178218159/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17819019902659043293/17820000000000000000 : ℝ)*(X 1 0+X 2 0)+(206097929009/712800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (4993/50000 : ℝ)) (hi := (8557/50000 : ℝ)) (c := (17819019902659043293/17820000000000000000 : ℝ)) (alpha := (206097929009/712800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17819019902659043293/17820000000000000000 : ℝ)*(X 0 1+X 2 1)+(206097929009/712800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (4993/50000 : ℝ)) (hi := (8557/50000 : ℝ)) (c := (17819019902659043293/17820000000000000000 : ℝ)) (alpha := (206097929009/712800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17819019902659043293/17820000000000000000 : ℝ)*(X 0 2+X 1 2)+(206097929009/712800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5271/1024 : ℝ)) (lo := (4993/50000 : ℝ)) (hi := (8557/50000 : ℝ)) (c := (17819019902659043293/17820000000000000000 : ℝ)) (alpha := (206097929009/712800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-551013823/5000000000 : ℝ)*X 0 0+(677352409/1250000000 : ℝ)*X 0 1+(1354704623/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612770323/5000000000 : ℝ)*X 1 0+(-344149753/2500000000 : ℝ)*X 1 1+(2709409593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612770607/5000000000 : ℝ)*X 2 0+(2709409289/5000000000 : ℝ)*X 2 1+(-688299537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4490766791/10000000000 : ℝ)*X 0 0+(984814923/2500000000 : ℝ)*X 0 1+(3939259503/10000000000 : ℝ)*X 0 2+(4490766791/10000000000 : ℝ)*X 1 0+(984814923/2500000000 : ℝ)*X 1 1+(3939259503/10000000000 : ℝ)*X 1 2+(4490766791/10000000000 : ℝ)*X 2 0+(984814923/2500000000 : ℝ)*X 2 1+(3939259503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-352927689/2000000000 : ℝ)*X 0 0+(1294334867/2500000000 : ℝ)*X 0 1+(5177339623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5389424269/10000000000 : ℝ)*X 1 0+(-185356771/1250000000 : ℝ)*X 1 1+(2588670071/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1077884867/2000000000 : ℝ)*X 2 0+(5177340087/10000000000 : ℝ)*X 2 1+(-1482854153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1855450837/5000000000 : ℝ)*X 0 0+(4328360037/10000000000 : ℝ)*X 0 1+(4328360291/10000000000 : ℝ)*X 0 2+(1855450837/5000000000 : ℝ)*X 1 0+(4328360037/10000000000 : ℝ)*X 1 1+(4328360291/10000000000 : ℝ)*X 1 2+(1855450837/5000000000 : ℝ)*X 2 0+(4328360037/10000000000 : ℝ)*X 2 1+(4328360291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-64886757/400000000 : ℝ)*X 0 0+(399941/800000 : ℝ)*X 0 1+(682710797/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((51964661/100000000 : ℝ)*X 1 0+(-339237133/2500000000 : ℝ)*X 1 1+(682710853/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598233551/5000000000 : ℝ)*X 2 0+(27308429/50000000 : ℝ)*X 2 1+(-67847429/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1156054677/2500000000 : ℝ)*X 0 0+(1935001741/5000000000 : ℝ)*X 0 1+(774001073/2000000000 : ℝ)*X 0 2+(1156054677/2500000000 : ℝ)*X 1 0+(1935001741/5000000000 : ℝ)*X 1 1+(774001073/2000000000 : ℝ)*X 1 2+(1156054677/2500000000 : ℝ)*X 2 0+(1935001741/5000000000 : ℝ)*X 2 1+(774001073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1239130869/10000000000 : ℝ)*X 0 0+(1117682333/2000000000 : ℝ)*X 0 1+(2576092991/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5406526061/10000000000 : ℝ)*X 1 0+(-746735721/5000000000 : ℝ)*X 1 1+(5152185853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1351631533/2500000000 : ℝ)*X 2 0+(2576092851/5000000000 : ℝ)*X 2 1+(-29869431/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3626682121/10000000000 : ℝ)*X 0 0+(873756431/2000000000 : ℝ)*X 0 1+(43687817/100000000 : ℝ)*X 0 2+(3626682121/10000000000 : ℝ)*X 1 0+(873756431/2000000000 : ℝ)*X 1 1+(43687817/100000000 : ℝ)*X 1 2+(3626682121/10000000000 : ℝ)*X 2 0+(873756431/2000000000 : ℝ)*X 2 1+(43687817/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1707_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66719/100000 : ℝ) ≤ (-2641971742270802714345244491/3960000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1792577/20000000000000 : ℝ)*(upper1) + (8259019/100000000000000 : ℝ)*(upper2) + (228001/800000000000 : ℝ)*(upper3) + (35794747/50000000000000 : ℝ)*(upper5) + (1349038775906583/100000000000000 : ℝ)*(major0) + (1349038775906583/100000000000000 : ℝ)*(major1) + (1349038775906583/100000000000000 : ℝ)*(major2) + (68860517/50000000000000 : ℝ)*(sp3) + (2024827750963443/100000000000000 : ℝ)*(sp4) + (80991749613353/4000000000000 : ℝ)*(sp5) + (1012403191987763/50000000000000 : ℝ)*(sp6) + (173872120627017/25000000000000 : ℝ)*(sp7) + (17005314809/50000000000000 : ℝ)*(sp13) + (21366987917/100000000000000 : ℝ)*(sp14) + (347744310114551/50000000000000 : ℝ)*(f.failure) + (2024827750963443/100000000000000 : ℝ)*(f.sum) + (40203664087669/11880000000000000000000000000 : ℝ)*base65 + (66745606643199101/22000000000000000000000000000000 : ℝ)*base68 + (43361971885199101/22000000000000000000000000000000 : ℝ)*base70 + (94588027774800899/22000000000000000000000000000000 : ℝ)*base71 + (8995178272691/11880000000000000000000000000 : ℝ)*base74 + (38766331184800899/22000000000000000000000000000000 : ℝ)*base75 + (140667057892800899/22000000000000000000000000000000 : ℝ)*base77 + (11565320427199101/22000000000000000000000000000000 : ℝ)*base80 + (67801828987811/11880000000000000000000000000 : ℝ)*base82 + (2597209/625000000000000000000 : ℝ)*base90 + (2597209/625000000000000000000 : ℝ)*base92 + (2597209/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (14583/25000 : ℝ) ≤ (2406303112633445696540622424999/4125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13661933/100000000000000 : ℝ)*(lower1) + (3997513/25000000000000 : ℝ)*(lower2) + (42069707/100000000000000 : ℝ)*(upper4) + (181623019788471/12500000000000 : ℝ)*(major0) + (181623019788471/12500000000000 : ℝ)*(major1) + (181623019788471/12500000000000 : ℝ)*(major2) + (1068721160113077/50000000000000 : ℝ)*(sp0) + (42748831459183/2000000000000 : ℝ)*(sp1) + (1068722719166557/50000000000000 : ℝ)*(sp2) + (749075719720683/100000000000000 : ℝ)*(sp3) + (2424507013/50000000000000 : ℝ)*(sp5) + (491820031/50000000000000 : ℝ)*(sp6) + (650642113/50000000000000 : ℝ)*(sp7) + (2050873511/50000000000000 : ℝ)*(sp8) + (749077021004909/100000000000000 : ℝ)*(f.failure) + (267180802746647/12500000000000 : ℝ)*(f.sum) + (1841284460029/742500000000000000000000000 : ℝ)*base65 + (22985939618712963/2750000000000000000000000000000 : ℝ)*base67 + (13305165578962963/2750000000000000000000000000000 : ℝ)*base69 + (1330759962963/2750000000000000000000000000000 : ℝ)*base71 + (3621567960863/1485000000000000000000000000 : ℝ)*base73 + (13382518810962963/2750000000000000000000000000000 : ℝ)*base75 + (15337362261962963/2750000000000000000000000000000 : ℝ)*base77 + (8128673024212963/2750000000000000000000000000000 : ℝ)*base79 + (337591684351/185625000000000000000000000 : ℝ)*base81 + (14202931/1250000000000000000000 : ℝ)*base90 + (14202931/1250000000000000000000 : ℝ)*base92 + (14202931/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (10173/12500 : ℝ) ≤ (610395966148736808717702084893/750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38250401/100000000000000 : ℝ)*(upper0) + (237661/800000000000 : ℝ)*(lower1) + (189651637/100000000000000 : ℝ)*(lower3) + (16015959/50000000000000 : ℝ)*(upper4) + (368763319711101/25000000000000 : ℝ)*(major0) + (368763319711101/25000000000000 : ℝ)*(major1) + (368763319711101/25000000000000 : ℝ)*(major2) + (3598965891/100000000000000 : ℝ)*(sp0) + (793877009/1250000000000 : ℝ)*(sp1) + (1310514573/6250000000000 : ℝ)*(sp3) + (1081259814569047/50000000000000 : ℝ)*(sp8) + (67576866185727/3125000000000 : ℝ)*(sp9) + (135157701756499/6250000000000 : ℝ)*(sp10) + (9505420646813/1250000000000 : ℝ)*(sp11) + (23764206874319/3125000000000 : ℝ)*(f.failure) + (135157701756499/6250000000000 : ℝ)*(f.sum) + (1265080480463/2970000000000000000000000000 : ℝ)*base65 + (22266583476167647/5500000000000000000000000000000 : ℝ)*base68 + (4885367602167647/5500000000000000000000000000000 : ℝ)*base70 + (38247233403832353/5500000000000000000000000000000 : ℝ)*base71 + (7267403625743/2970000000000000000000000000 : ℝ)*base73 + (28128581827832353/5500000000000000000000000000000 : ℝ)*base75 + (9431859739832353/5500000000000000000000000000000 : ℝ)*base77 + (31308361859832353/5500000000000000000000000000000 : ℝ)*base79 + (3358895695823/2970000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (127621/39062500000000000000 : ℝ)*base90 + (127621/39062500000000000000 : ℝ)*base92 + (127621/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-4519/5000 : ℝ) ≤ (-53684401314583678053872922474233/59400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1984247/10000000000000 : ℝ)*(upper1) + (50415599/100000000000000 : ℝ)*(upper3) + (4964493/25000000000000 : ℝ)*(upper5) + (304794175197581/20000000000000 : ℝ)*(major0) + (304794175197581/20000000000000 : ℝ)*(major1) + (304794175197581/20000000000000 : ℝ)*(major2) + (2501808863/100000000000000 : ℝ)*(sp4) + (1650761489/6250000000000 : ℝ)*(sp5) + (35929302703/100000000000000 : ℝ)*(sp6) + (195598559/1562500000000 : ℝ)*(sp7) + (114619569568109/5000000000000 : ℝ)*(sp12) + (114618374049361/5000000000000 : ℝ)*(sp13) + (114617898193417/5000000000000 : ℝ)*(sp14) + (785661267160611/100000000000000 : ℝ)*(sp15) + (785673785468387/100000000000000 : ℝ)*(f.failure) + (573098473292761/25000000000000 : ℝ)*(f.sum) + (6193535276771/7128000000000000000000000000 : ℝ)*base66 + (9979901505335793/4400000000000000000000000000000 : ℝ)*base67 + (25602533039735793/4400000000000000000000000000000 : ℝ)*base69 + (8076550226664207/4400000000000000000000000000000 : ℝ)*base72 + (9083092784869/7128000000000000000000000000 : ℝ)*base73 + (677004899864207/4400000000000000000000000000000 : ℝ)*base76 + (18965087213735793/4400000000000000000000000000000 : ℝ)*base77 + (3802762374535793/4400000000000000000000000000000 : ℝ)*base79 + (78279415958267/7128000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3416733/1250000000000000000000 : ℝ)*base90 + (3416733/1250000000000000000000 : ℝ)*base92 + (3416733/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1707_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8557/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66719/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14583/25000 : ℝ) else (10173/12500 : ℝ) ≤ X j i ∧ X j i ≤ (4519/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1707_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1707_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66719/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14583/25000 : ℝ) else (10173/12500 : ℝ) ≤ X j i ∧ X j i ≤ (4519/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1707_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1707_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5271/1024 : ℝ) ≤ p) (hpb : p ≤ (5279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24246241/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17127/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66719/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14583/25000 : ℝ) else (10173/12500 : ℝ) ≤ X j i ∧ X j i ≤ (4519/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1707_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
