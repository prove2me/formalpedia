-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:09.46849+00:00
-- url     : https://prove2.me/submissions/b3d183d7-9bd6-4677-9e2c-0cf9e4b8b427

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
theorem support_rectangle_w1033_s3_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107458713/5000000000 : ℝ)*x 0 + (2720710201/5000000000 : ℝ)*x 1 + (1305184797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107458713/5000000000 : ℝ)^4113 ≤ (13438299198127/100000000000000 : ℝ)^3089 := by
    have hnat : (1107458713 : ℕ)^4113*100000000000000^3089 ≤ 13438299198127^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107458713 5000000000 13438299198127 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720710201/5000000000 : ℝ)^4113 ≤ (44473488936393/100000000000000 : ℝ)^3089 := by
    have hnat : (2720710201 : ℕ)^4113*100000000000000^3089 ≤ 44473488936393^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720710201 5000000000 44473488936393 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305184797/2500000000 : ℝ)^4113 ≤ (21044105925617/50000000000000 : ℝ)^3089 := by
    have hnat : (1305184797 : ℕ)^4113*50000000000000^3089 ≤ 21044105925617^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305184797 2500000000 21044105925617 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107458713/5000000000 : ℝ), (2720710201/5000000000 : ℝ), (1305184797/2500000000 : ℝ)] ![(13438299198127/100000000000000 : ℝ), (44473488936393/100000000000000 : ℝ), (21044105925617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107458713/5000000000 : ℝ)|^4113 ≤ (13438299198127/100000000000000 : ℝ)^3089
        have hw : |(-1107458713/5000000000 : ℝ)|=(1107458713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720710201/5000000000 : ℝ)|^4113 ≤ (44473488936393/100000000000000 : ℝ)^3089
        have hw : |(2720710201/5000000000 : ℝ)|=(2720710201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305184797/2500000000 : ℝ)|^4113 ≤ (21044105925617/50000000000000 : ℝ)^3089
        have hw : |(1305184797/2500000000 : ℝ)|=(1305184797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678269471/5000000000 : ℝ)*x 0 + (-2328017997/10000000000 : ℝ)*x 1 + (1305184909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678269471/5000000000 : ℝ)^4113 ≤ (21776080457221/50000000000000 : ℝ)^3089 := by
    have hnat : (2678269471 : ℕ)^4113*50000000000000^3089 ≤ 21776080457221^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678269471 5000000000 21776080457221 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2328017997/10000000000 : ℝ)^4113 ≤ (14359622407559/100000000000000 : ℝ)^3089 := by
    have hnat : (2328017997 : ℕ)^4113*100000000000000^3089 ≤ 14359622407559^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2328017997 10000000000 14359622407559 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305184909/2500000000 : ℝ)^4113 ≤ (5261027082519/12500000000000 : ℝ)^3089 := by
    have hnat : (1305184909 : ℕ)^4113*12500000000000^3089 ≤ 5261027082519^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305184909 2500000000 5261027082519 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678269471/5000000000 : ℝ), (-2328017997/10000000000 : ℝ), (1305184909/2500000000 : ℝ)] ![(21776080457221/50000000000000 : ℝ), (14359622407559/100000000000000 : ℝ), (5261027082519/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678269471/5000000000 : ℝ)|^4113 ≤ (21776080457221/50000000000000 : ℝ)^3089
        have hw : |(2678269471/5000000000 : ℝ)|=(2678269471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2328017997/10000000000 : ℝ)|^4113 ≤ (14359622407559/100000000000000 : ℝ)^3089
        have hw : |(-2328017997/10000000000 : ℝ)|=(2328017997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305184909/2500000000 : ℝ)|^4113 ≤ (5261027082519/12500000000000 : ℝ)^3089
        have hw : |(1305184909/2500000000 : ℝ)|=(1305184909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339134793/2500000000 : ℝ)*x 0 + (1044147907/2000000000 : ℝ)*x 1 + (-1164008913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339134793/2500000000 : ℝ)^4113 ≤ (43552163404411/100000000000000 : ℝ)^3089 := by
    have hnat : (1339134793 : ℕ)^4113*100000000000000^3089 ≤ 43552163404411^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339134793 2500000000 43552163404411 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044147907/2000000000 : ℝ)^4113 ≤ (21044107787999/50000000000000 : ℝ)^3089 := by
    have hnat : (1044147907 : ℕ)^4113*50000000000000^3089 ≤ 21044107787999^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044147907 2000000000 21044107787999 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1164008913/5000000000 : ℝ)^4113 ≤ (287192420063/2000000000000 : ℝ)^3089 := by
    have hnat : (1164008913 : ℕ)^4113*2000000000000^3089 ≤ 287192420063^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164008913 5000000000 287192420063 2000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339134793/2500000000 : ℝ), (1044147907/2000000000 : ℝ), (-1164008913/5000000000 : ℝ)] ![(43552163404411/100000000000000 : ℝ), (21044107787999/50000000000000 : ℝ), (287192420063/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339134793/2500000000 : ℝ)|^4113 ≤ (43552163404411/100000000000000 : ℝ)^3089
        have hw : |(1339134793/2500000000 : ℝ)|=(1339134793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044147907/2000000000 : ℝ)|^4113 ≤ (21044107787999/50000000000000 : ℝ)^3089
        have hw : |(1044147907/2000000000 : ℝ)|=(1044147907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1164008913/5000000000 : ℝ)|^4113 ≤ (287192420063/2000000000000 : ℝ)^3089
        have hw : |(-1164008913/5000000000 : ℝ)|=(1164008913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094297209/2500000000 : ℝ)*x 0 + (2083864019/5000000000 : ℝ)*x 1 + (1149349657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094297209/2500000000 : ℝ)^4113 ≤ (1664262892763/5000000000000 : ℝ)^3089 := by
    have hnat : (1094297209 : ℕ)^4113*5000000000000^3089 ≤ 1664262892763^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094297209 2500000000 1664262892763 5000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083864019/5000000000 : ℝ)^4113 ≤ (15590729923233/50000000000000 : ℝ)^3089 := by
    have hnat : (2083864019 : ℕ)^4113*50000000000000^3089 ≤ 15590729923233^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083864019 5000000000 15590729923233 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149349657/2500000000 : ℝ)^4113 ≤ (35533282275959/100000000000000 : ℝ)^3089 := by
    have hnat : (1149349657 : ℕ)^4113*100000000000000^3089 ≤ 35533282275959^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149349657 2500000000 35533282275959 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094297209/2500000000 : ℝ), (2083864019/5000000000 : ℝ), (1149349657/2500000000 : ℝ)] ![(1664262892763/5000000000000 : ℝ), (15590729923233/50000000000000 : ℝ), (35533282275959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094297209/2500000000 : ℝ)|^4113 ≤ (1664262892763/5000000000000 : ℝ)^3089
        have hw : |(1094297209/2500000000 : ℝ)|=(1094297209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2083864019/5000000000 : ℝ)|^4113 ≤ (15590729923233/50000000000000 : ℝ)^3089
        have hw : |(2083864019/5000000000 : ℝ)|=(2083864019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1149349657/2500000000 : ℝ)|^4113 ≤ (35533282275959/100000000000000 : ℝ)^3089
        have hw : |(1149349657/2500000000 : ℝ)|=(1149349657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-276867817/1250000000 : ℝ)*x 0 + (522166627/1000000000 : ℝ)*x 1 + (5440487263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276867817/1250000000 : ℝ)^4113 ≤ (6719251024083/50000000000000 : ℝ)^3089 := by
    have hnat : (276867817 : ℕ)^4113*50000000000000^3089 ≤ 6719251024083^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276867817 1250000000 6719251024083 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522166627/1000000000 : ℝ)^4113 ≤ (21049081809231/50000000000000 : ℝ)^3089 := by
    have hnat : (522166627 : ℕ)^4113*50000000000000^3089 ≤ 21049081809231^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522166627 1000000000 21049081809231 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440487263/10000000000 : ℝ)^4113 ≤ (1778533372617/4000000000000 : ℝ)^3089 := by
    have hnat : (5440487263 : ℕ)^4113*4000000000000^3089 ≤ 1778533372617^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440487263 10000000000 1778533372617 4000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276867817/1250000000 : ℝ), (522166627/1000000000 : ℝ), (5440487263/10000000000 : ℝ)] ![(6719251024083/50000000000000 : ℝ), (21049081809231/50000000000000 : ℝ), (1778533372617/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276867817/1250000000 : ℝ)|^4113 ≤ (6719251024083/50000000000000 : ℝ)^3089
        have hw : |(-276867817/1250000000 : ℝ)|=(276867817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522166627/1000000000 : ℝ)|^4113 ≤ (21049081809231/50000000000000 : ℝ)^3089
        have hw : |(522166627/1000000000 : ℝ)|=(522166627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440487263/10000000000 : ℝ)|^4113 ≤ (1778533372617/4000000000000 : ℝ)^3089
        have hw : |(5440487263/10000000000 : ℝ)|=(5440487263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16565921/31250000 : ℝ)*x 0 + (-131766883/625000000 : ℝ)*x 1 + (1360121883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16565921/31250000 : ℝ)^4113 ≤ (10738239099457/25000000000000 : ℝ)^3089 := by
    have hnat : (16565921 : ℕ)^4113*25000000000000^3089 ≤ 10738239099457^3089*31250000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16565921 31250000 10738239099457 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131766883/625000000 : ℝ)^4113 ≤ (629185317217/5000000000000 : ℝ)^3089 := by
    have hnat : (131766883 : ℕ)^4113*5000000000000^3089 ≤ 629185317217^3089*625000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131766883 625000000 629185317217 5000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360121883/2500000000 : ℝ)^4113 ≤ (44463337242659/100000000000000 : ℝ)^3089 := by
    have hnat : (1360121883 : ℕ)^4113*100000000000000^3089 ≤ 44463337242659^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360121883 2500000000 44463337242659 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16565921/31250000 : ℝ), (-131766883/625000000 : ℝ), (1360121883/2500000000 : ℝ)] ![(10738239099457/25000000000000 : ℝ), (629185317217/5000000000000 : ℝ), (44463337242659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16565921/31250000 : ℝ)|^4113 ≤ (10738239099457/25000000000000 : ℝ)^3089
        have hw : |(16565921/31250000 : ℝ)|=(16565921/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131766883/625000000 : ℝ)|^4113 ≤ (629185317217/5000000000000 : ℝ)^3089
        have hw : |(-131766883/625000000 : ℝ)|=(131766883/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360121883/2500000000 : ℝ)|^4113 ≤ (44463337242659/100000000000000 : ℝ)^3089
        have hw : |(1360121883/2500000000 : ℝ)|=(1360121883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301094569/10000000000 : ℝ)*x 0 + (5440487429/10000000000 : ℝ)*x 1 + (-84330819/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301094569/10000000000 : ℝ)^4113 ≤ (21476477384369/50000000000000 : ℝ)^3089 := by
    have hnat : (5301094569 : ℕ)^4113*50000000000000^3089 ≤ 21476477384369^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301094569 10000000000 21476477384369 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440487429/10000000000 : ℝ)^4113 ≤ (22231668060911/50000000000000 : ℝ)^3089 := by
    have hnat : (5440487429 : ℕ)^4113*50000000000000^3089 ≤ 22231668060911^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440487429 10000000000 22231668060911 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84330819/400000000 : ℝ)^4113 ≤ (503348364083/4000000000000 : ℝ)^3089 := by
    have hnat : (84330819 : ℕ)^4113*4000000000000^3089 ≤ 503348364083^3089*400000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84330819 400000000 503348364083 4000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301094569/10000000000 : ℝ), (5440487429/10000000000 : ℝ), (-84330819/400000000 : ℝ)] ![(21476477384369/50000000000000 : ℝ), (22231668060911/50000000000000 : ℝ), (503348364083/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301094569/10000000000 : ℝ)|^4113 ≤ (21476477384369/50000000000000 : ℝ)^3089
        have hw : |(5301094569/10000000000 : ℝ)|=(5301094569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440487429/10000000000 : ℝ)|^4113 ≤ (22231668060911/50000000000000 : ℝ)^3089
        have hw : |(5440487429/10000000000 : ℝ)|=(5440487429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84330819/400000000 : ℝ)|^4113 ≤ (503348364083/4000000000000 : ℝ)^3089
        have hw : |(-84330819/400000000 : ℝ)|=(84330819/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s3_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094309129/2500000000 : ℝ)*x 0 + (574449351/1250000000 : ℝ)*x 1 + (2084771391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094309129/2500000000 : ℝ)^4113 ≤ (33285740618813/100000000000000 : ℝ)^3089 := by
    have hnat : (1094309129 : ℕ)^4113*100000000000000^3089 ≤ 33285740618813^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094309129 2500000000 33285740618813 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574449351/1250000000 : ℝ)^4113 ≤ (35514720098671/100000000000000 : ℝ)^3089 := by
    have hnat : (574449351 : ℕ)^4113*100000000000000^3089 ≤ 35514720098671^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574449351 1250000000 35514720098671 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084771391/5000000000 : ℝ)^4113 ≤ (3899942408769/12500000000000 : ℝ)^3089 := by
    have hnat : (2084771391 : ℕ)^4113*12500000000000^3089 ≤ 3899942408769^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084771391 5000000000 3899942408769 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094309129/2500000000 : ℝ), (574449351/1250000000 : ℝ), (2084771391/5000000000 : ℝ)] ![(33285740618813/100000000000000 : ℝ), (35514720098671/100000000000000 : ℝ), (3899942408769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094309129/2500000000 : ℝ)|^4113 ≤ (33285740618813/100000000000000 : ℝ)^3089
        have hw : |(1094309129/2500000000 : ℝ)|=(1094309129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574449351/1250000000 : ℝ)|^4113 ≤ (35514720098671/100000000000000 : ℝ)^3089
        have hw : |(574449351/1250000000 : ℝ)|=(574449351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084771391/5000000000 : ℝ)|^4113 ≤ (3899942408769/12500000000000 : ℝ)^3089
        have hw : |(2084771391/5000000000 : ℝ)|=(2084771391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2057/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7477/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1053/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8551/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1053/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8551/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1053/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8551/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1053/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8551/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1053/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8551/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1053/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8551/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8551/100000 : ℝ) ^ (8225/2048 : ℝ) ≤ (642345856159751/12500000000000000000 : ℝ) := by
    have hpowers : (8551/100000 : ℝ)^8225 ≤ (642345856159751/12500000000000000000 : ℝ)^2048 := by
      have hnat : (8551 : ℕ)^8225*12500000000000000000^2048 ≤ 642345856159751^2048*100000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8551 100000 642345856159751 12500000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8551/100000 : ℝ)) (X := (642345856159751/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1053/6250 : ℝ) ^ (8225/2048 : ℝ) ≤ (78294376773376703/100000000000000000000 : ℝ) := by
    have hpowers : (1053/6250 : ℝ)^8225 ≤ (78294376773376703/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1053 : ℕ)^8225*100000000000000000000^2048 ≤ 78294376773376703^2048*6250^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1053 6250 78294376773376703 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1053/6250 : ℝ)) (X := (78294376773376703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250642345856159751/6250000000000000000 : ℝ) ≤ (976587489999/976562500000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (6250642345856159751/6250000000000000000 : ℝ)^2048 ≤ (976587489999/976562500000 : ℝ)^8225 := by
      have hnat : (6250642345856159751 : ℕ)^2048*976562500000^8225 ≤ 976587489999^8225*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250642345856159751 6250000000000000000 976587489999 976562500000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (976587489999/976562500000 : ℝ)) (X := (6250642345856159751/6250000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100083433143622654711/100000000000000000000 : ℝ) ≤ (10002076809380279/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (100083433143622654711/100000000000000000000 : ℝ)^2048 ≤ (10002076809380279/10000000000000000 : ℝ)^8225 := by
      have hnat : (100083433143622654711 : ℕ)^2048*10000000000000000^8225 ≤ 10002076809380279^8225*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083433143622654711 100000000000000000000 10002076809380279 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002076809380279/10000000000000000 : ℝ)) (X := (100083433143622654711/100000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50078294376773376703/50000000000000000000 : ℝ) ≤ (5001948860585399/5000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50078294376773376703/50000000000000000000 : ℝ)^2048 ≤ (5001948860585399/5000000000000000 : ℝ)^8225 := by
      have hnat : (50078294376773376703 : ℕ)^2048*5000000000000000^8225 ≤ 5001948860585399^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078294376773376703 50000000000000000000 5001948860585399 5000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001948860585399/5000000000000000 : ℝ)) (X := (50078294376773376703/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(642345856159751/12500000000000000000 : ℝ) ≤ ((41470490974430391391/41485000000000000000 : ℝ)+2*(1820911790519/829700000000000 : ℝ)*(8551/100000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (41470490974430391391/41485000000000000000 : ℝ)+2*(1820911790519/829700000000000 : ℝ)*(8551/100000 : ℝ)=(976587489999/976562500000 : ℝ) by norm_num, show 1+2*(642345856159751/12500000000000000000 : ℝ)=(6250642345856159751/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78294376773376703/100000000000000000000 : ℝ)+(642345856159751/12500000000000000000 : ℝ) ≤ ((41470490974430391391/41485000000000000000 : ℝ)+(1820911790519/829700000000000 : ℝ)*((1053/6250 : ℝ)+(8551/100000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (41470490974430391391/41485000000000000000 : ℝ)+(1820911790519/829700000000000 : ℝ)*((1053/6250 : ℝ)+(8551/100000 : ℝ))=(10002076809380279/10000000000000000 : ℝ) by norm_num, show 1+(78294376773376703/100000000000000000000 : ℝ)+(642345856159751/12500000000000000000 : ℝ)=(100083433143622654711/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78294376773376703/100000000000000000000 : ℝ) ≤ ((41470490974430391391/41485000000000000000 : ℝ)+2*(1820911790519/829700000000000 : ℝ)*(1053/6250 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (41470490974430391391/41485000000000000000 : ℝ)+2*(1820911790519/829700000000000 : ℝ)*(1053/6250 : ℝ)=(5001948860585399/5000000000000000 : ℝ) by norm_num, show 1+2*(78294376773376703/100000000000000000000 : ℝ)=(50078294376773376703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41470490974430391391/41485000000000000000 : ℝ)*(X 1 0+X 2 0)+(1820911790519/829700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (8551/100000 : ℝ)) (hi := (1053/6250 : ℝ)) (c := (41470490974430391391/41485000000000000000 : ℝ)) (alpha := (1820911790519/829700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41470490974430391391/41485000000000000000 : ℝ)*(X 0 1+X 2 1)+(1820911790519/829700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (8551/100000 : ℝ)) (hi := (1053/6250 : ℝ)) (c := (41470490974430391391/41485000000000000000 : ℝ)) (alpha := (1820911790519/829700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41470490974430391391/41485000000000000000 : ℝ)*(X 0 2+X 1 2)+(1820911790519/829700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (8551/100000 : ℝ)) (hi := (1053/6250 : ℝ)) (c := (41470490974430391391/41485000000000000000 : ℝ)) (alpha := (1820911790519/829700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1107458713/5000000000 : ℝ)*X 0 0+(2720710201/5000000000 : ℝ)*X 0 1+(1305184797/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678269471/5000000000 : ℝ)*X 1 0+(-2328017997/10000000000 : ℝ)*X 1 1+(1305184909/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339134793/2500000000 : ℝ)*X 2 0+(1044147907/2000000000 : ℝ)*X 2 1+(-1164008913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1094297209/2500000000 : ℝ)*X 0 0+(2083864019/5000000000 : ℝ)*X 0 1+(1149349657/2500000000 : ℝ)*X 0 2+(1094297209/2500000000 : ℝ)*X 1 0+(2083864019/5000000000 : ℝ)*X 1 1+(1149349657/2500000000 : ℝ)*X 1 2+(1094297209/2500000000 : ℝ)*X 2 0+(2083864019/5000000000 : ℝ)*X 2 1+(1149349657/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-276867817/1250000000 : ℝ)*X 0 0+(522166627/1000000000 : ℝ)*X 0 1+(5440487263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16565921/31250000 : ℝ)*X 1 0+(-131766883/625000000 : ℝ)*X 1 1+(1360121883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301094569/10000000000 : ℝ)*X 2 0+(5440487429/10000000000 : ℝ)*X 2 1+(-84330819/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1094309129/2500000000 : ℝ)*X 0 0+(574449351/1250000000 : ℝ)*X 0 1+(2084771391/5000000000 : ℝ)*X 0 2+(1094309129/2500000000 : ℝ)*X 1 0+(574449351/1250000000 : ℝ)*X 1 1+(2084771391/5000000000 : ℝ)*X 1 2+(1094309129/2500000000 : ℝ)*X 2 0+(574449351/1250000000 : ℝ)*X 2 1+(2084771391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7849042990902283943883928731/1037125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1638758067/100000000000000 : ℝ)*(base19) + (1494161463/100000000000000 : ℝ)*(base23) + (57781303/25000000000000 : ℝ)*(lower2) + (66760871/100000000000000 : ℝ)*(upper3) + (49446909/100000000000000 : ℝ)*(lower4) + (1714724549071247/50000000000000 : ℝ)*(major0) + (1714724549071247/50000000000000 : ℝ)*(major1) + (1714724549071247/50000000000000 : ℝ)*(major2) + (226573131555389/5000000000000 : ℝ)*(sp0) + (906300566740547/20000000000000 : ℝ)*(sp1) + (4531502978299339/100000000000000 : ℝ)*(sp2) + (1163688770604447/50000000000000 : ℝ)*(sp3) + (41841353023/100000000000000 : ℝ)*(sp4) + (497823313/3125000000000 : ℝ)*(sp7) + (232739347155491/10000000000000 : ℝ)*(f.failure) + (2265752236230401/50000000000000 : ℝ)*(f.sum) + (106839978945933/20742500000000000000000000000 : ℝ)*base65 + (4841189772633415423/2074250000000000000000000000000000 : ℝ)*base68 + (17840651346386165423/2074250000000000000000000000000000 : ℝ)*base70 + (19866263040128415423/2074250000000000000000000000000000 : ℝ)*base72 + (5683872353461/41485000000000000000000000000 : ℝ)*base73 + (19412099210617084577/2074250000000000000000000000000000 : ℝ)*base75 + (9942638135774915423/2074250000000000000000000000000000 : ℝ)*base78 + (14102716446937834577/2074250000000000000000000000000000 : ℝ)*base79 + (13148118603333/5185625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (433067/125000000000000000000 : ℝ)*base89 + (433067/125000000000000000000 : ℝ)*base91 + (433067/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3441915920565829200258892029/518562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1628461487/100000000000000 : ℝ)*(base19) + (1482086841/100000000000000 : ℝ)*(base23) + (834797/10000000000000 : ℝ)*(upper2) + (63229863/25000000000000 : ℝ)*(upper3) + (6000429/12500000000000 : ℝ)*(upper5) + (1729267891431127/50000000000000 : ℝ)*(major0) + (1729267891431127/50000000000000 : ℝ)*(major1) + (1729267891431127/50000000000000 : ℝ)*(major2) + (27873346777/100000000000000 : ℝ)*(sp1) + (6204620631/25000000000000 : ℝ)*(sp2) + (571242276580981/12500000000000 : ℝ)*(sp4) + (142809647213737/3125000000000 : ℝ)*(sp5) + (4569911912078483/100000000000000 : ℝ)*(sp6) + (1173566565914693/50000000000000 : ℝ)*(sp7) + (1173566565914693/50000000000000 : ℝ)*(f.failure) + (571242276580981/12500000000000 : ℝ)*(f.sum) + (133094437113773/20742500000000000000000000000 : ℝ)*base65 + (897183291488122343/2074250000000000000000000000000000 : ℝ)*base68 + (35155279153182877657/2074250000000000000000000000000000 : ℝ)*base69 + (36203618141918377657/2074250000000000000000000000000000 : ℝ)*base71 + (109720766678669/41485000000000000000000000000 : ℝ)*base74 + (26625009338359877657/2074250000000000000000000000000000 : ℝ)*base75 + (34634650171249127657/2074250000000000000000000000000000 : ℝ)*base77 + (27133008257677127657/2074250000000000000000000000000000 : ℝ)*base79 + (242889531089371/41485000000000000000000000000 : ℝ)*base81 + (9758659/625000000000000000000 : ℝ)*base90 + (9758659/625000000000000000000 : ℝ)*base92 + (9758659/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1033_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2057/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7477/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s4_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-554731643/2500000000 : ℝ)*x 0 + (5407683371/10000000000 : ℝ)*x 1 + (5251858383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (554731643/2500000000 : ℝ)^4113 ≤ (841918535077/6250000000000 : ℝ)^3089 := by
    have hnat : (554731643 : ℕ)^4113*6250000000000^3089 ≤ 841918535077^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554731643 2500000000 841918535077 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407683371/10000000000 : ℝ)^4113 ≤ (44106722631887/100000000000000 : ℝ)^3089 := by
    have hnat : (5407683371 : ℕ)^4113*100000000000000^3089 ≤ 44106722631887^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407683371 10000000000 44106722631887 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5251858383/10000000000 : ℝ)^4113 ≤ (21211290395091/50000000000000 : ℝ)^3089 := by
    have hnat : (5251858383 : ℕ)^4113*50000000000000^3089 ≤ 21211290395091^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251858383 10000000000 21211290395091 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-554731643/2500000000 : ℝ), (5407683371/10000000000 : ℝ), (5251858383/10000000000 : ℝ)] ![(841918535077/6250000000000 : ℝ), (44106722631887/100000000000000 : ℝ), (21211290395091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-554731643/2500000000 : ℝ)|^4113 ≤ (841918535077/6250000000000 : ℝ)^3089
        have hw : |(-554731643/2500000000 : ℝ)|=(554731643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407683371/10000000000 : ℝ)|^4113 ≤ (44106722631887/100000000000000 : ℝ)^3089
        have hw : |(5407683371/10000000000 : ℝ)|=(5407683371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5251858383/10000000000 : ℝ)|^4113 ≤ (21211290395091/50000000000000 : ℝ)^3089
        have hw : |(5251858383/10000000000 : ℝ)|=(5251858383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348211827/10000000000 : ℝ)*x 0 + (-287277023/1250000000 : ℝ)*x 1 + (2625929221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348211827/10000000000 : ℝ)^4113 ≤ (43462035173593/100000000000000 : ℝ)^3089 := by
    have hnat : (5348211827 : ℕ)^4113*100000000000000^3089 ≤ 43462035173593^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348211827 10000000000 43462035173593 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287277023/1250000000 : ℝ)^4113 ≤ (7057691693021/50000000000000 : ℝ)^3089 := by
    have hnat : (287277023 : ℕ)^4113*50000000000000^3089 ≤ 7057691693021^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287277023 1250000000 7057691693021 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2625929221/5000000000 : ℝ)^4113 ≤ (10605645356187/25000000000000 : ℝ)^3089 := by
    have hnat : (2625929221 : ℕ)^4113*25000000000000^3089 ≤ 10605645356187^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625929221 5000000000 10605645356187 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348211827/10000000000 : ℝ), (-287277023/1250000000 : ℝ), (2625929221/5000000000 : ℝ)] ![(43462035173593/100000000000000 : ℝ), (7057691693021/50000000000000 : ℝ), (10605645356187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348211827/10000000000 : ℝ)|^4113 ≤ (43462035173593/100000000000000 : ℝ)^3089
        have hw : |(5348211827/10000000000 : ℝ)|=(5348211827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-287277023/1250000000 : ℝ)|^4113 ≤ (7057691693021/50000000000000 : ℝ)^3089
        have hw : |(-287277023/1250000000 : ℝ)|=(287277023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2625929221/5000000000 : ℝ)|^4113 ≤ (10605645356187/25000000000000 : ℝ)^3089
        have hw : |(2625929221/5000000000 : ℝ)|=(2625929221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674105967/5000000000 : ℝ)*x 0 + (2625929159/5000000000 : ℝ)*x 1 + (-1149108103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674105967/5000000000 : ℝ)^4113 ≤ (43462036331373/100000000000000 : ℝ)^3089 := by
    have hnat : (2674105967 : ℕ)^4113*100000000000000^3089 ≤ 43462036331373^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674105967 5000000000 43462036331373 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2625929159/5000000000 : ℝ)^4113 ≤ (10605645022771/25000000000000 : ℝ)^3089 := by
    have hnat : (2625929159 : ℕ)^4113*25000000000000^3089 ≤ 10605645022771^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625929159 5000000000 10605645022771 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149108103/5000000000 : ℝ)^4113 ≤ (3528845891489/25000000000000 : ℝ)^3089 := by
    have hnat : (1149108103 : ℕ)^4113*25000000000000^3089 ≤ 3528845891489^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149108103 5000000000 3528845891489 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674105967/5000000000 : ℝ), (2625929159/5000000000 : ℝ), (-1149108103/5000000000 : ℝ)] ![(43462036331373/100000000000000 : ℝ), (10605645022771/25000000000000 : ℝ), (3528845891489/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674105967/5000000000 : ℝ)|^4113 ≤ (43462036331373/100000000000000 : ℝ)^3089
        have hw : |(2674105967/5000000000 : ℝ)|=(2674105967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2625929159/5000000000 : ℝ)|^4113 ≤ (10605645022771/25000000000000 : ℝ)^3089
        have hw : |(2625929159/5000000000 : ℝ)|=(2625929159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1149108103/5000000000 : ℝ)|^4113 ≤ (3528845891489/25000000000000 : ℝ)^3089
        have hw : |(-1149108103/5000000000 : ℝ)|=(1149108103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379568139/10000000000 : ℝ)*x 0 + (2115275789/5000000000 : ℝ)*x 1 + (1813579/4000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379568139/10000000000 : ℝ)^4113 ≤ (6661870120429/20000000000000 : ℝ)^3089 := by
    have hnat : (4379568139 : ℕ)^4113*20000000000000^3089 ≤ 6661870120429^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379568139 10000000000 6661870120429 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115275789/5000000000 : ℝ)^4113 ≤ (15904426941219/50000000000000 : ℝ)^3089 := by
    have hnat : (2115275789 : ℕ)^4113*50000000000000^3089 ≤ 15904426941219^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115275789 5000000000 15904426941219 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1813579/4000000 : ℝ)^4113 ≤ (34881795501061/100000000000000 : ℝ)^3089 := by
    have hnat : (1813579 : ℕ)^4113*100000000000000^3089 ≤ 34881795501061^3089*4000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813579 4000000 34881795501061 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379568139/10000000000 : ℝ), (2115275789/5000000000 : ℝ), (1813579/4000000 : ℝ)] ![(6661870120429/20000000000000 : ℝ), (15904426941219/50000000000000 : ℝ), (34881795501061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379568139/10000000000 : ℝ)|^4113 ≤ (6661870120429/20000000000000 : ℝ)^3089
        have hw : |(4379568139/10000000000 : ℝ)|=(4379568139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115275789/5000000000 : ℝ)|^4113 ≤ (15904426941219/50000000000000 : ℝ)^3089
        have hw : |(2115275789/5000000000 : ℝ)|=(2115275789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1813579/4000000 : ℝ)|^4113 ≤ (34881795501061/100000000000000 : ℝ)^3089
        have hw : |(1813579/4000000 : ℝ)|=(1813579/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109467389/5000000000 : ℝ)*x 0 + (65654023/125000000 : ℝ)*x 1 + (675902283/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109467389/5000000000 : ℝ)^4113 ≤ (6735381446357/50000000000000 : ℝ)^3089 := by
    have hnat : (1109467389 : ℕ)^4113*50000000000000^3089 ≤ 6735381446357^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109467389 5000000000 6735381446357 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65654023/125000000 : ℝ)^4113 ≤ (42427565509147/100000000000000 : ℝ)^3089 := by
    have hnat : (65654023 : ℕ)^4113*100000000000000^3089 ≤ 42427565509147^3089*125000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65654023 125000000 42427565509147 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675902283/1250000000 : ℝ)^4113 ≤ (44101671589429/100000000000000 : ℝ)^3089 := by
    have hnat : (675902283 : ℕ)^4113*100000000000000^3089 ≤ 44101671589429^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675902283 1250000000 44101671589429 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109467389/5000000000 : ℝ), (65654023/125000000 : ℝ), (675902283/1250000000 : ℝ)] ![(6735381446357/50000000000000 : ℝ), (42427565509147/100000000000000 : ℝ), (44101671589429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109467389/5000000000 : ℝ)|^4113 ≤ (6735381446357/50000000000000 : ℝ)^3089
        have hw : |(-1109467389/5000000000 : ℝ)|=(1109467389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65654023/125000000 : ℝ)|^4113 ≤ (42427565509147/100000000000000 : ℝ)^3089
        have hw : |(65654023/125000000 : ℝ)|=(65654023/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675902283/1250000000 : ℝ)|^4113 ≤ (44101671589429/100000000000000 : ℝ)^3089
        have hw : |(675902283/1250000000 : ℝ)|=(675902283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309068817/10000000000 : ℝ)*x 0 + (-26785703/125000000 : ℝ)*x 1 + (5407218367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309068817/10000000000 : ℝ)^4113 ≤ (43039007818277/100000000000000 : ℝ)^3089 := by
    have hnat : (5309068817 : ℕ)^4113*100000000000000^3089 ≤ 43039007818277^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309068817 10000000000 43039007818277 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26785703/125000000 : ℝ)^4113 ≤ (3214829865281/25000000000000 : ℝ)^3089 := by
    have hnat : (26785703 : ℕ)^4113*25000000000000^3089 ≤ 3214829865281^3089*125000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26785703 125000000 3214829865281 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407218367/10000000000 : ℝ)^4113 ≤ (11025418176997/25000000000000 : ℝ)^3089 := by
    have hnat : (5407218367 : ℕ)^4113*25000000000000^3089 ≤ 11025418176997^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407218367 10000000000 11025418176997 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309068817/10000000000 : ℝ), (-26785703/125000000 : ℝ), (5407218367/10000000000 : ℝ)] ![(43039007818277/100000000000000 : ℝ), (3214829865281/25000000000000 : ℝ), (11025418176997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309068817/10000000000 : ℝ)|^4113 ≤ (43039007818277/100000000000000 : ℝ)^3089
        have hw : |(5309068817/10000000000 : ℝ)|=(5309068817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26785703/125000000 : ℝ)|^4113 ≤ (3214829865281/25000000000000 : ℝ)^3089
        have hw : |(-26785703/125000000 : ℝ)|=(26785703/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407218367/10000000000 : ℝ)|^4113 ≤ (11025418176997/25000000000000 : ℝ)^3089
        have hw : |(5407218367/10000000000 : ℝ)|=(5407218367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309068469/10000000000 : ℝ)*x 0 + (2703609397/5000000000 : ℝ)*x 1 + (-214285613/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309068469/10000000000 : ℝ)^4113 ≤ (8607800812389/20000000000000 : ℝ)^3089 := by
    have hnat : (5309068469 : ℕ)^4113*20000000000000^3089 ≤ 8607800812389^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309068469 10000000000 8607800812389 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703609397/5000000000 : ℝ)^4113 ≤ (352813418761/800000000000 : ℝ)^3089 := by
    have hnat : (2703609397 : ℕ)^4113*800000000000^3089 ≤ 352813418761^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703609397 5000000000 352813418761 800000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214285613/1000000000 : ℝ)^4113 ≤ (6429659291093/50000000000000 : ℝ)^3089 := by
    have hnat : (214285613 : ℕ)^4113*50000000000000^3089 ≤ 6429659291093^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214285613 1000000000 6429659291093 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309068469/10000000000 : ℝ), (2703609397/5000000000 : ℝ), (-214285613/1000000000 : ℝ)] ![(8607800812389/20000000000000 : ℝ), (352813418761/800000000000 : ℝ), (6429659291093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309068469/10000000000 : ℝ)|^4113 ≤ (8607800812389/20000000000000 : ℝ)^3089
        have hw : |(5309068469/10000000000 : ℝ)|=(5309068469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703609397/5000000000 : ℝ)|^4113 ≤ (352813418761/800000000000 : ℝ)^3089
        have hw : |(2703609397/5000000000 : ℝ)|=(2703609397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214285613/1000000000 : ℝ)|^4113 ≤ (6429659291093/50000000000000 : ℝ)^3089
        have hw : |(-214285613/1000000000 : ℝ)|=(214285613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s4_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379585159/10000000000 : ℝ)*x 0 + (453304621/1000000000 : ℝ)*x 1 + (2115728261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379585159/10000000000 : ℝ)^4113 ≤ (33309522961759/100000000000000 : ℝ)^3089 := by
    have hnat : (4379585159 : ℕ)^4113*100000000000000^3089 ≤ 33309522961759^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379585159 10000000000 33309522961759 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453304621/1000000000 : ℝ)^4113 ≤ (2179535195443/6250000000000 : ℝ)^3089 := by
    have hnat : (453304621 : ℕ)^4113*6250000000000^3089 ≤ 2179535195443^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453304621 1000000000 2179535195443 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115728261/5000000000 : ℝ)^4113 ≤ (31817913897713/100000000000000 : ℝ)^3089 := by
    have hnat : (2115728261 : ℕ)^4113*100000000000000^3089 ≤ 31817913897713^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115728261 5000000000 31817913897713 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379585159/10000000000 : ℝ), (453304621/1000000000 : ℝ), (2115728261/5000000000 : ℝ)] ![(33309522961759/100000000000000 : ℝ), (2179535195443/6250000000000 : ℝ), (31817913897713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379585159/10000000000 : ℝ)|^4113 ≤ (33309522961759/100000000000000 : ℝ)^3089
        have hw : |(4379585159/10000000000 : ℝ)|=(4379585159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453304621/1000000000 : ℝ)|^4113 ≤ (2179535195443/6250000000000 : ℝ)^3089
        have hw : |(453304621/1000000000 : ℝ)|=(453304621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115728261/5000000000 : ℝ)|^4113 ≤ (31817913897713/100000000000000 : ℝ)^3089
        have hw : |(2115728261/5000000000 : ℝ)|=(2115728261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7477/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2057/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (219/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7477/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2057/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7477/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2057/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7477/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2057/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7477/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2057/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7477/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2057/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7477/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2057/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2057/20000 : ℝ) ^ (8225/2048 : ℝ) ≤ (10786996905055741/100000000000000000000 : ℝ) := by
    have hpowers : (2057/20000 : ℝ)^8225 ≤ (10786996905055741/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2057 : ℕ)^8225*100000000000000000000^2048 ≤ 10786996905055741^2048*20000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2057 20000 10786996905055741 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2057/20000 : ℝ)) (X := (10786996905055741/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7477/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (48498927944465279/100000000000000000000 : ℝ) := by
    have hpowers : (7477/50000 : ℝ)^8225 ≤ (48498927944465279/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7477 : ℕ)^8225*100000000000000000000^2048 ≤ 48498927944465279^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7477 50000 48498927944465279 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7477/50000 : ℝ)) (X := (48498927944465279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010786996905055741/50000000000000000000 : ℝ) ≤ (2000107428475223/2000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50010786996905055741/50000000000000000000 : ℝ)^2048 ≤ (2000107428475223/2000000000000000 : ℝ)^8225 := by
      have hnat : (50010786996905055741 : ℕ)^2048*2000000000000000^8225 ≤ 2000107428475223^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010786996905055741 50000000000000000000 2000107428475223 2000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107428475223/2000000000000000 : ℝ)) (X := (50010786996905055741/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002964296242476051/5000000000000000000 : ℝ) ≤ (10001475872991073/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (5002964296242476051/5000000000000000000 : ℝ)^2048 ≤ (10001475872991073/10000000000000000 : ℝ)^8225 := by
      have hnat : (5002964296242476051 : ℕ)^2048*10000000000000000^8225 ≤ 10001475872991073^8225*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002964296242476051 5000000000000000000 10001475872991073 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001475872991073/10000000000000000 : ℝ)) (X := (5002964296242476051/5000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048498927944465279/50000000000000000000 : ℝ) ≤ (10002414603606031/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50048498927944465279/50000000000000000000 : ℝ)^2048 ≤ (10002414603606031/10000000000000000 : ℝ)^8225 := by
      have hnat : (50048498927944465279 : ℕ)^2048*10000000000000000^8225 ≤ 10002414603606031^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048498927944465279 50000000000000000000 10002414603606031 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002414603606031/10000000000000000 : ℝ)) (X := (50048498927944465279/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10786996905055741/100000000000000000000 : ℝ) ≤ ((373385585832035159/373520000000000000 : ℝ)+2*(469365307479/233450000000000 : ℝ)*(2057/20000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (373385585832035159/373520000000000000 : ℝ)+2*(469365307479/233450000000000 : ℝ)*(2057/20000 : ℝ)=(2000107428475223/2000000000000000 : ℝ) by norm_num, show 1+2*(10786996905055741/100000000000000000000 : ℝ)=(50010786996905055741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48498927944465279/100000000000000000000 : ℝ)+(10786996905055741/100000000000000000000 : ℝ) ≤ ((373385585832035159/373520000000000000 : ℝ)+(469365307479/233450000000000 : ℝ)*((7477/50000 : ℝ)+(2057/20000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (373385585832035159/373520000000000000 : ℝ)+(469365307479/233450000000000 : ℝ)*((7477/50000 : ℝ)+(2057/20000 : ℝ))=(10001475872991073/10000000000000000 : ℝ) by norm_num, show 1+(48498927944465279/100000000000000000000 : ℝ)+(10786996905055741/100000000000000000000 : ℝ)=(5002964296242476051/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48498927944465279/100000000000000000000 : ℝ) ≤ ((373385585832035159/373520000000000000 : ℝ)+2*(469365307479/233450000000000 : ℝ)*(7477/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (373385585832035159/373520000000000000 : ℝ)+2*(469365307479/233450000000000 : ℝ)*(7477/50000 : ℝ)=(10002414603606031/10000000000000000 : ℝ) by norm_num, show 1+2*(48498927944465279/100000000000000000000 : ℝ)=(50048498927944465279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (373385585832035159/373520000000000000 : ℝ)*(X 1 0+X 2 0)+(469365307479/233450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2057/20000 : ℝ)) (hi := (7477/50000 : ℝ)) (c := (373385585832035159/373520000000000000 : ℝ)) (alpha := (469365307479/233450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (373385585832035159/373520000000000000 : ℝ)*(X 0 1+X 2 1)+(469365307479/233450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2057/20000 : ℝ)) (hi := (7477/50000 : ℝ)) (c := (373385585832035159/373520000000000000 : ℝ)) (alpha := (469365307479/233450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (373385585832035159/373520000000000000 : ℝ)*(X 0 2+X 1 2)+(469365307479/233450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2057/20000 : ℝ)) (hi := (7477/50000 : ℝ)) (c := (373385585832035159/373520000000000000 : ℝ)) (alpha := (469365307479/233450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-554731643/2500000000 : ℝ)*X 0 0+(5407683371/10000000000 : ℝ)*X 0 1+(5251858383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348211827/10000000000 : ℝ)*X 1 0+(-287277023/1250000000 : ℝ)*X 1 1+(2625929221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674105967/5000000000 : ℝ)*X 2 0+(2625929159/5000000000 : ℝ)*X 2 1+(-1149108103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379568139/10000000000 : ℝ)*X 0 0+(2115275789/5000000000 : ℝ)*X 0 1+(1813579/4000000 : ℝ)*X 0 2+(4379568139/10000000000 : ℝ)*X 1 0+(2115275789/5000000000 : ℝ)*X 1 1+(1813579/4000000 : ℝ)*X 1 2+(4379568139/10000000000 : ℝ)*X 2 0+(2115275789/5000000000 : ℝ)*X 2 1+(1813579/4000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1109467389/5000000000 : ℝ)*X 0 0+(65654023/125000000 : ℝ)*X 0 1+(675902283/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309068817/10000000000 : ℝ)*X 1 0+(-26785703/125000000 : ℝ)*X 1 1+(5407218367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309068469/10000000000 : ℝ)*X 2 0+(2703609397/5000000000 : ℝ)*X 2 1+(-214285613/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379585159/10000000000 : ℝ)*X 0 0+(453304621/1000000000 : ℝ)*X 0 1+(2115728261/5000000000 : ℝ)*X 0 2+(4379585159/10000000000 : ℝ)*X 1 0+(453304621/1000000000 : ℝ)*X 1 1+(2115728261/5000000000 : ℝ)*X 1 2+(4379585159/10000000000 : ℝ)*X 2 0+(453304621/1000000000 : ℝ)*X 2 1+(2115728261/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1513435406840534204781/291812500000000000000000000 : ℝ) := by norm_num
    linear_combination (1103221767/100000000000000 : ℝ)*(base19) + (611144091/50000000000000 : ℝ)*(base23) + (4988109/100000000000000 : ℝ)*(lower2) + (64908343/50000000000000 : ℝ)*(upper3) + (5945003/5000000000000 : ℝ)*(upper5) + (485678112615627/10000000000000 : ℝ)*(major0) + (485678112615627/10000000000000 : ℝ)*(major1) + (485678112615627/10000000000000 : ℝ)*(major2) + (1604370706858991/25000000000000 : ℝ)*(sp0) + (3208754761188861/50000000000000 : ℝ)*(sp1) + (6417509403311307/100000000000000 : ℝ)*(sp2) + (3296036889162957/100000000000000 : ℝ)*(sp3) + (1111926541/4000000000000 : ℝ)*(sp4) + (14564672483/100000000000000 : ℝ)*(sp7) + (41200643172943/1250000000000 : ℝ)*(f.failure) + (6417510625599489/100000000000000 : ℝ)*(f.sum) + (496263221877/2334500000000000000000000000 : ℝ)*base65 + (427637181181507/3735200000000000000000000000000 : ℝ)*base68 + (6222243150144893/3735200000000000000000000000000 : ℝ)*base69 + (29194931576989693/3735200000000000000000000000000 : ℝ)*base71 + (229659043597/46690000000000000000000000 : ℝ)*base74 + (28256350829637507/3735200000000000000000000000000 : ℝ)*base76 + (2104199642720893/3735200000000000000000000000000 : ℝ)*base77 + (19373919921147907/3735200000000000000000000000000 : ℝ)*base80 + (3330253576109/1167250000000000000000000000 : ℝ)*base81 + (34091/15625000000000000000 : ℝ)*base89 + (34091/15625000000000000000 : ℝ)*base91 + (34091/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109160601828839029261046229/18676000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19278627/100000000000000 : ℝ)*(base19) + (82955843/20000000000000 : ℝ)*(base23) + (61966909/100000000000000 : ℝ)*(upper3) + (44421483/12500000000000 : ℝ)*(lower4) + (4885844680038341/100000000000000 : ℝ)*(major0) + (4885844680038341/100000000000000 : ℝ)*(major1) + (4885844680038341/100000000000000 : ℝ)*(major2) + (430717703/50000000000000 : ℝ)*(sp1) + (1319502179/6250000000000 : ℝ)*(sp2) + (1918276569/25000000000000 : ℝ)*(sp3) + (3227956874431481/50000000000000 : ℝ)*(sp4) + (100873638564827/1562500000000 : ℝ)*(sp5) + (3227946111024441/50000000000000 : ℝ)*(sp6) + (663153548655041/20000000000000 : ℝ)*(sp7) + (3315775416381481/100000000000000 : ℝ)*(f.failure) + (3227956874431481/50000000000000 : ℝ)*(f.sum) + (49260497045243/23345000000000000000000000000 : ℝ)*base65 + (101209312854157619/37352000000000000000000000000000 : ℝ)*base67 + (296957387365517619/37352000000000000000000000000000 : ℝ)*base69 + (241020417215029619/37352000000000000000000000000000 : ℝ)*base71 + (27887735803863/5836250000000000000000000000 : ℝ)*base74 + (123187663684397619/37352000000000000000000000000000 : ℝ)*base75 + (840548266682037619/37352000000000000000000000000000 : ℝ)*base77 + (629299472057197619/37352000000000000000000000000000 : ℝ)*base79 + (192436516301/2918125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4005697/1250000000000000000000 : ℝ)*base89 + (4005697/1250000000000000000000 : ℝ)*base91 + (4005697/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1033_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7477/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2057/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s5_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-443970901/2000000000 : ℝ)*x 0 + (5397961241/10000000000 : ℝ)*x 1 + (1315243053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443970901/2000000000 : ℝ)^4113 ≤ (13478197828553/100000000000000 : ℝ)^3089 := by
    have hnat : (443970901 : ℕ)^4113*100000000000000^3089 ≤ 13478197828553^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443970901 2000000000 13478197828553 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397961241/10000000000 : ℝ)^4113 ≤ (1760046827169/4000000000000 : ℝ)^3089 := by
    have hnat : (5397961241 : ℕ)^4113*4000000000000^3089 ≤ 1760046827169^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397961241 10000000000 1760046827169 4000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315243053/2500000000 : ℝ)^4113 ≤ (8504126293913/20000000000000 : ℝ)^3089 := by
    have hnat : (1315243053 : ℕ)^4113*20000000000000^3089 ≤ 8504126293913^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315243053 2500000000 8504126293913 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443970901/2000000000 : ℝ), (5397961241/10000000000 : ℝ), (1315243053/2500000000 : ℝ)] ![(13478197828553/100000000000000 : ℝ), (1760046827169/4000000000000 : ℝ), (8504126293913/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443970901/2000000000 : ℝ)|^4113 ≤ (13478197828553/100000000000000 : ℝ)^3089
        have hw : |(-443970901/2000000000 : ℝ)|=(443970901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397961241/10000000000 : ℝ)|^4113 ≤ (1760046827169/4000000000000 : ℝ)^3089
        have hw : |(5397961241/10000000000 : ℝ)|=(5397961241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315243053/2500000000 : ℝ)|^4113 ≤ (8504126293913/20000000000000 : ℝ)^3089
        have hw : |(1315243053/2500000000 : ℝ)|=(1315243053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345798971/10000000000 : ℝ)*x 0 + (-1144706651/5000000000 : ℝ)*x 1 + (1315243041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345798971/10000000000 : ℝ)^4113 ≤ (678686392539/1562500000000 : ℝ)^3089 := by
    have hnat : (5345798971 : ℕ)^4113*1562500000000^3089 ≤ 678686392539^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345798971 10000000000 678686392539 1562500000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144706651/5000000000 : ℝ)^4113 ≤ (7021719953417/50000000000000 : ℝ)^3089 := by
    have hnat : (1144706651 : ℕ)^4113*50000000000000^3089 ≤ 7021719953417^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144706651 5000000000 7021719953417 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315243041/2500000000 : ℝ)^4113 ≤ (42520630953011/100000000000000 : ℝ)^3089 := by
    have hnat : (1315243041 : ℕ)^4113*100000000000000^3089 ≤ 42520630953011^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315243041 2500000000 42520630953011 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345798971/10000000000 : ℝ), (-1144706651/5000000000 : ℝ), (1315243041/2500000000 : ℝ)] ![(678686392539/1562500000000 : ℝ), (7021719953417/50000000000000 : ℝ), (42520630953011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345798971/10000000000 : ℝ)|^4113 ≤ (678686392539/1562500000000 : ℝ)^3089
        have hw : |(5345798971/10000000000 : ℝ)|=(5345798971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1144706651/5000000000 : ℝ)|^4113 ≤ (7021719953417/50000000000000 : ℝ)^3089
        have hw : |(-1144706651/5000000000 : ℝ)|=(1144706651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315243041/2500000000 : ℝ)|^4113 ≤ (42520630953011/100000000000000 : ℝ)^3089
        have hw : |(1315243041/2500000000 : ℝ)|=(1315243041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069159777/2000000000 : ℝ)*x 0 + (5260971981/10000000000 : ℝ)*x 1 + (-1144706829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069159777/2000000000 : ℝ)^4113 ≤ (43435928192083/100000000000000 : ℝ)^3089 := by
    have hnat : (1069159777 : ℕ)^4113*100000000000000^3089 ≤ 43435928192083^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069159777 2000000000 43435928192083 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260971981/10000000000 : ℝ)^4113 ≤ (42520628983649/100000000000000 : ℝ)^3089 := by
    have hnat : (5260971981 : ℕ)^4113*100000000000000^3089 ≤ 42520628983649^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260971981 10000000000 42520628983649 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144706829/5000000000 : ℝ)^4113 ≤ (1404344281447/10000000000000 : ℝ)^3089 := by
    have hnat : (1144706829 : ℕ)^4113*10000000000000^3089 ≤ 1404344281447^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144706829 5000000000 1404344281447 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069159777/2000000000 : ℝ), (5260971981/10000000000 : ℝ), (-1144706829/5000000000 : ℝ)] ![(43435928192083/100000000000000 : ℝ), (42520628983649/100000000000000 : ℝ), (1404344281447/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069159777/2000000000 : ℝ)|^4113 ≤ (43435928192083/100000000000000 : ℝ)^3089
        have hw : |(1069159777/2000000000 : ℝ)|=(1069159777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260971981/10000000000 : ℝ)|^4113 ≤ (42520628983649/100000000000000 : ℝ)^3089
        have hw : |(5260971981/10000000000 : ℝ)|=(5260971981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144706829/5000000000 : ℝ)|^4113 ≤ (1404344281447/10000000000000 : ℝ)^3089
        have hw : |(-1144706829/5000000000 : ℝ)|=(1144706829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4380105551/10000000000 : ℝ)*x 0 + (4248817997/10000000000 : ℝ)*x 1 + (4515539247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380105551/10000000000 : ℝ)^4113 ≤ (16657396509931/50000000000000 : ℝ)^3089 := by
    have hnat : (4380105551 : ℕ)^4113*50000000000000^3089 ≤ 16657396509931^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380105551 10000000000 16657396509931 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248817997/10000000000 : ℝ)^4113 ≤ (7997963950213/25000000000000 : ℝ)^3089 := by
    have hnat : (4248817997 : ℕ)^4113*25000000000000^3089 ≤ 7997963950213^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248817997 10000000000 7997963950213 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515539247/10000000000 : ℝ)^4113 ≤ (17346675581143/50000000000000 : ℝ)^3089 := by
    have hnat : (4515539247 : ℕ)^4113*50000000000000^3089 ≤ 17346675581143^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515539247 10000000000 17346675581143 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380105551/10000000000 : ℝ), (4248817997/10000000000 : ℝ), (4515539247/10000000000 : ℝ)] ![(16657396509931/50000000000000 : ℝ), (7997963950213/25000000000000 : ℝ), (17346675581143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380105551/10000000000 : ℝ)|^4113 ≤ (16657396509931/50000000000000 : ℝ)^3089
        have hw : |(4380105551/10000000000 : ℝ)|=(4380105551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248817997/10000000000 : ℝ)|^4113 ≤ (7997963950213/25000000000000 : ℝ)^3089
        have hw : |(4248817997/10000000000 : ℝ)|=(4248817997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515539247/10000000000 : ℝ)|^4113 ≤ (17346675581143/50000000000000 : ℝ)^3089
        have hw : |(4515539247/10000000000 : ℝ)|=(4515539247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2219860397/10000000000 : ℝ)*x 0 + (1315332557/2500000000 : ℝ)*x 1 + (5397601867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219860397/10000000000 : ℝ)^4113 ≤ (2695649092379/20000000000000 : ℝ)^3089 := by
    have hnat : (2219860397 : ℕ)^4113*20000000000000^3089 ≤ 2695649092379^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219860397 10000000000 2695649092379 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315332557/2500000000 : ℝ)^4113 ≤ (42524484317189/100000000000000 : ℝ)^3089 := by
    have hnat : (1315332557 : ℕ)^4113*100000000000000^3089 ≤ 42524484317189^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315332557 2500000000 42524484317189 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397601867/10000000000 : ℝ)^4113 ≤ (274982938797/625000000000 : ℝ)^3089 := by
    have hnat : (5397601867 : ℕ)^4113*625000000000^3089 ≤ 274982938797^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397601867 10000000000 274982938797 625000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2219860397/10000000000 : ℝ), (1315332557/2500000000 : ℝ), (5397601867/10000000000 : ℝ)] ![(2695649092379/20000000000000 : ℝ), (42524484317189/100000000000000 : ℝ), (274982938797/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2219860397/10000000000 : ℝ)|^4113 ≤ (2695649092379/20000000000000 : ℝ)^3089
        have hw : |(-2219860397/10000000000 : ℝ)|=(2219860397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315332557/2500000000 : ℝ)|^4113 ≤ (42524484317189/100000000000000 : ℝ)^3089
        have hw : |(1315332557/2500000000 : ℝ)|=(1315332557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397601867/10000000000 : ℝ)|^4113 ≤ (274982938797/625000000000 : ℝ)^3089
        have hw : |(5397601867/10000000000 : ℝ)|=(5397601867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311385637/10000000000 : ℝ)*x 0 + (-430556959/2000000000 : ℝ)*x 1 + (1349400451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311385637/10000000000 : ℝ)^4113 ≤ (10766004378383/25000000000000 : ℝ)^3089 := by
    have hnat : (5311385637 : ℕ)^4113*25000000000000^3089 ≤ 10766004378383^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311385637 10000000000 10766004378383 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430556959/2000000000 : ℝ)^4113 ≤ (3234678235851/25000000000000 : ℝ)^3089 := by
    have hnat : (430556959 : ℕ)^4113*25000000000000^3089 ≤ 3234678235851^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430556959 2000000000 3234678235851 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349400451/2500000000 : ℝ)^4113 ≤ (10999317380939/25000000000000 : ℝ)^3089 := by
    have hnat : (1349400451 : ℕ)^4113*25000000000000^3089 ≤ 10999317380939^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349400451 2500000000 10999317380939 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311385637/10000000000 : ℝ), (-430556959/2000000000 : ℝ), (1349400451/2500000000 : ℝ)] ![(10766004378383/25000000000000 : ℝ), (3234678235851/25000000000000 : ℝ), (10999317380939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311385637/10000000000 : ℝ)|^4113 ≤ (10766004378383/25000000000000 : ℝ)^3089
        have hw : |(5311385637/10000000000 : ℝ)|=(5311385637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430556959/2000000000 : ℝ)|^4113 ≤ (3234678235851/25000000000000 : ℝ)^3089
        have hw : |(-430556959/2000000000 : ℝ)|=(430556959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349400451/2500000000 : ℝ)|^4113 ≤ (10999317380939/25000000000000 : ℝ)^3089
        have hw : |(1349400451/2500000000 : ℝ)|=(1349400451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311385983/10000000000 : ℝ)*x 0 + (2698800859/5000000000 : ℝ)*x 1 + (-1076392223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311385983/10000000000 : ℝ)^4113 ≤ (2691501328051/6250000000000 : ℝ)^3089 := by
    have hnat : (5311385983 : ℕ)^4113*6250000000000^3089 ≤ 2691501328051^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311385983 10000000000 2691501328051 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698800859/5000000000 : ℝ)^4113 ≤ (10999317147591/25000000000000 : ℝ)^3089 := by
    have hnat : (2698800859 : ℕ)^4113*25000000000000^3089 ≤ 10999317147591^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698800859 5000000000 10999317147591 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076392223/5000000000 : ℝ)^4113 ≤ (404334692203/3125000000000 : ℝ)^3089 := by
    have hnat : (1076392223 : ℕ)^4113*3125000000000^3089 ≤ 404334692203^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076392223 5000000000 404334692203 3125000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311385983/10000000000 : ℝ), (2698800859/5000000000 : ℝ), (-1076392223/5000000000 : ℝ)] ![(2691501328051/6250000000000 : ℝ), (10999317147591/25000000000000 : ℝ), (404334692203/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311385983/10000000000 : ℝ)|^4113 ≤ (2691501328051/6250000000000 : ℝ)^3089
        have hw : |(5311385983/10000000000 : ℝ)|=(5311385983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698800859/5000000000 : ℝ)|^4113 ≤ (10999317147591/25000000000000 : ℝ)^3089
        have hw : |(2698800859/5000000000 : ℝ)|=(2698800859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076392223/5000000000 : ℝ)|^4113 ≤ (404334692203/3125000000000 : ℝ)^3089
        have hw : |(-1076392223/5000000000 : ℝ)|=(1076392223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s5_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1095029091/2500000000 : ℝ)*x 0 + (4514842567/10000000000 : ℝ)*x 1 + (4249517921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095029091/2500000000 : ℝ)^4113 ≤ (16657451263159/50000000000000 : ℝ)^3089 := by
    have hnat : (1095029091 : ℕ)^4113*50000000000000^3089 ≤ 16657451263159^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095029091 2500000000 16657451263159 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514842567/10000000000 : ℝ)^4113 ≤ (34686224278641/100000000000000 : ℝ)^3089 := by
    have hnat : (4514842567 : ℕ)^4113*100000000000000^3089 ≤ 34686224278641^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514842567 10000000000 34686224278641 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249517921/10000000000 : ℝ)^4113 ≤ (31998873178511/100000000000000 : ℝ)^3089 := by
    have hnat : (4249517921 : ℕ)^4113*100000000000000^3089 ≤ 31998873178511^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249517921 10000000000 31998873178511 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095029091/2500000000 : ℝ), (4514842567/10000000000 : ℝ), (4249517921/10000000000 : ℝ)] ![(16657451263159/50000000000000 : ℝ), (34686224278641/100000000000000 : ℝ), (31998873178511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095029091/2500000000 : ℝ)|^4113 ≤ (16657451263159/50000000000000 : ℝ)^3089
        have hw : |(1095029091/2500000000 : ℝ)|=(1095029091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514842567/10000000000 : ℝ)|^4113 ≤ (34686224278641/100000000000000 : ℝ)^3089
        have hw : |(4514842567/10000000000 : ℝ)|=(4514842567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249517921/10000000000 : ℝ)|^4113 ≤ (31998873178511/100000000000000 : ℝ)^3089
        have hw : |(4249517921/10000000000 : ℝ)|=(4249517921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (1393/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (219/2000 : ℝ) ^ (8225/2048 : ℝ) ≤ (3468313089233873/25000000000000000000 : ℝ) := by
    have hpowers : (219/2000 : ℝ)^8225 ≤ (3468313089233873/25000000000000000000 : ℝ)^2048 := by
      have hnat : (219 : ℕ)^8225*25000000000000000000^2048 ≤ 3468313089233873^2048*2000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        219 2000 3468313089233873 25000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (219/2000 : ℝ)) (X := (3468313089233873/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14249/100000 : ℝ) ^ (8225/2048 : ℝ) ≤ (19974330890729589/50000000000000000000 : ℝ) := by
    have hpowers : (14249/100000 : ℝ)^8225 ≤ (19974330890729589/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14249 : ℕ)^8225*50000000000000000000^2048 ≤ 19974330890729589^2048*100000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14249 100000 19974330890729589 50000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14249/100000 : ℝ)) (X := (19974330890729589/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503468313089233873/12500000000000000000 : ℝ) ≤ (2500172701890927/2500000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (12503468313089233873/12500000000000000000 : ℝ)^2048 ≤ (2500172701890927/2500000000000000 : ℝ)^8225 := by
      have hnat : (12503468313089233873 : ℕ)^2048*2500000000000000^8225 ≤ 2500172701890927^8225*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503468313089233873 12500000000000000000 2500172701890927 2500000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500172701890927/2500000000000000 : ℝ)) (X := (12503468313089233873/12500000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005382191413839467/10000000000000000000 : ℝ) ≤ (10001339878540859/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (10005382191413839467/10000000000000000000 : ℝ)^2048 ≤ (10001339878540859/10000000000000000 : ℝ)^8225 := by
      have hnat : (10005382191413839467 : ℕ)^2048*10000000000000000^8225 ≤ 10001339878540859^8225*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005382191413839467 10000000000000000000 10001339878540859 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001339878540859/10000000000000000 : ℝ)) (X := (10005382191413839467/10000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019974330890729589/25000000000000000000 : ℝ) ≤ (1000198894951801/1000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (25019974330890729589/25000000000000000000 : ℝ)^2048 ≤ (1000198894951801/1000000000000000 : ℝ)^8225 := by
      have hnat : (25019974330890729589 : ℕ)^2048*1000000000000000^8225 ≤ 1000198894951801^8225*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019974330890729589 25000000000000000000 1000198894951801 1000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000198894951801/1000000000000000 : ℝ)) (X := (25019974330890729589/25000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3468313089233873/25000000000000000000 : ℝ) ≤ ((515282254996141653/515468750000000000 : ℝ)+2*(649070977151/329900000000000 : ℝ)*(219/2000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (515282254996141653/515468750000000000 : ℝ)+2*(649070977151/329900000000000 : ℝ)*(219/2000 : ℝ)=(2500172701890927/2500000000000000 : ℝ) by norm_num, show 1+2*(3468313089233873/25000000000000000000 : ℝ)=(12503468313089233873/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19974330890729589/50000000000000000000 : ℝ)+(3468313089233873/25000000000000000000 : ℝ) ≤ ((515282254996141653/515468750000000000 : ℝ)+(649070977151/329900000000000 : ℝ)*((14249/100000 : ℝ)+(219/2000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (515282254996141653/515468750000000000 : ℝ)+(649070977151/329900000000000 : ℝ)*((14249/100000 : ℝ)+(219/2000 : ℝ))=(10001339878540859/10000000000000000 : ℝ) by norm_num, show 1+(19974330890729589/50000000000000000000 : ℝ)+(3468313089233873/25000000000000000000 : ℝ)=(10005382191413839467/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19974330890729589/50000000000000000000 : ℝ) ≤ ((515282254996141653/515468750000000000 : ℝ)+2*(649070977151/329900000000000 : ℝ)*(14249/100000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (515282254996141653/515468750000000000 : ℝ)+2*(649070977151/329900000000000 : ℝ)*(14249/100000 : ℝ)=(1000198894951801/1000000000000000 : ℝ) by norm_num, show 1+2*(19974330890729589/50000000000000000000 : ℝ)=(25019974330890729589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (515282254996141653/515468750000000000 : ℝ)*(X 1 0+X 2 0)+(649070977151/329900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (515282254996141653/515468750000000000 : ℝ)) (alpha := (649070977151/329900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (515282254996141653/515468750000000000 : ℝ)*(X 0 1+X 2 1)+(649070977151/329900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (515282254996141653/515468750000000000 : ℝ)) (alpha := (649070977151/329900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (515282254996141653/515468750000000000 : ℝ)*(X 0 2+X 1 2)+(649070977151/329900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (515282254996141653/515468750000000000 : ℝ)) (alpha := (649070977151/329900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443970901/2000000000 : ℝ)*X 0 0+(5397961241/10000000000 : ℝ)*X 0 1+(1315243053/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345798971/10000000000 : ℝ)*X 1 0+(-1144706651/5000000000 : ℝ)*X 1 1+(1315243041/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069159777/2000000000 : ℝ)*X 2 0+(5260971981/10000000000 : ℝ)*X 2 1+(-1144706829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4380105551/10000000000 : ℝ)*X 0 0+(4248817997/10000000000 : ℝ)*X 0 1+(4515539247/10000000000 : ℝ)*X 0 2+(4380105551/10000000000 : ℝ)*X 1 0+(4248817997/10000000000 : ℝ)*X 1 1+(4515539247/10000000000 : ℝ)*X 1 2+(4380105551/10000000000 : ℝ)*X 2 0+(4248817997/10000000000 : ℝ)*X 2 1+(4515539247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2219860397/10000000000 : ℝ)*X 0 0+(1315332557/2500000000 : ℝ)*X 0 1+(5397601867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311385637/10000000000 : ℝ)*X 1 0+(-430556959/2000000000 : ℝ)*X 1 1+(1349400451/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311385983/10000000000 : ℝ)*X 2 0+(2698800859/5000000000 : ℝ)*X 2 1+(-1076392223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1095029091/2500000000 : ℝ)*X 0 0+(4514842567/10000000000 : ℝ)*X 0 1+(4249517921/10000000000 : ℝ)*X 0 2+(1095029091/2500000000 : ℝ)*X 1 0+(4514842567/10000000000 : ℝ)*X 1 1+(4249517921/10000000000 : ℝ)*X 1 2+(1095029091/2500000000 : ℝ)*X 2 0+(4514842567/10000000000 : ℝ)*X 2 1+(4249517921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22878603607720008895568733/3221679687500000000000000000000 : ℝ) := by norm_num
    linear_combination (1016648063/50000000000000 : ℝ)*(base19) + (2117687509/100000000000000 : ℝ)*(base23) + (60703723/100000000000000 : ℝ)*(upper3) + (145425701/100000000000000 : ℝ)*(lower4) + (2762321332668523/50000000000000 : ℝ)*(major0) + (2762321332668523/50000000000000 : ℝ)*(major1) + (2762321332668523/50000000000000 : ℝ)*(major2) + (57030674290823/781250000000 : ℝ)*(sp0) + (7299987793693187/100000000000000 : ℝ)*(sp1) + (7299976802964987/100000000000000 : ℝ)*(sp2) + (1874632210193421/50000000000000 : ℝ)*(sp3) + (496232531/781250000000 : ℝ)*(sp4) + (2181267363/20000000000000 : ℝ)*(sp6) + (30846582857/100000000000000 : ℝ)*(sp7) + (37492952669697/1000000000000 : ℝ)*(f.failure) + (28515585261677/390625000000 : ℝ)*(f.sum) + (22910574456079/4123750000000000000000000000 : ℝ)*base65 + (124595061039888553/12886718750000000000000000000000 : ℝ)*base68 + (315016807601230231/25773437500000000000000000000000 : ℝ)*base70 + (29834234316051019/25773437500000000000000000000000 : ℝ)*base71 + (7529112652041/16495000000000000000000000000 : ℝ)*base73 + (990053483536511481/25773437500000000000000000000000 : ℝ)*base76 + (682757141837773913/51546875000000000000000000000000 : ℝ)*base77 + (838958736485976087/51546875000000000000000000000000 : ℝ)*base80 + (59316807790121/16495000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (102089/12500000000000000000 : ℝ)*base89 + (102089/12500000000000000000 : ℝ)*base91 + (102089/12500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (766295943156931787056568829/51546875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286402543/100000000000000 : ℝ)*(base19) + (196843851/20000000000000 : ℝ)*(base23) + (44966099/100000000000000 : ℝ)*(upper2) + (1997/9765625000 : ℝ)*(upper3) + (123198279/100000000000000 : ℝ)*(upper5) + (5553631209897389/100000000000000 : ℝ)*(major0) + (5553631209897389/100000000000000 : ℝ)*(major1) + (5553631209897389/100000000000000 : ℝ)*(major2) + (2383572277/50000000000000 : ℝ)*(sp1) + (12810845729/50000000000000 : ℝ)*(sp2) + (3669146799887301/50000000000000 : ℝ)*(sp4) + (458643034139219/6250000000000 : ℝ)*(sp5) + (458641687116493/6250000000000 : ℝ)*(sp6) + (376896832448677/10000000000000 : ℝ)*(sp7) + (376896832448677/10000000000000 : ℝ)*(f.failure) + (3669146799887301/50000000000000 : ℝ)*(f.sum) + (3198624676169/16495000000000000000000000000 : ℝ)*base65 + (1869284738799815091/103093750000000000000000000000000 : ℝ)*base68 + (369598437929252591/103093750000000000000000000000000 : ℝ)*base70 + (659315706374315091/103093750000000000000000000000000 : ℝ)*base72 + (27244750476251/16495000000000000000000000000 : ℝ)*base74 + (452963151218690091/103093750000000000000000000000000 : ℝ)*base76 + (55939220521059909/103093750000000000000000000000000 : ℝ)*base77 + (1477809793086502591/103093750000000000000000000000000 : ℝ)*base80 + (89759252519471/16495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1146349/125000000000000000000 : ℝ)*base89 + (1146349/125000000000000000000 : ℝ)*base91 + (1146349/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1033_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1033_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1033_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1033_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1033_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
