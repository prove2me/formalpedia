-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1249_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:00.735348+00:00
-- url     : https://prove2.me/submissions/1f7676dc-7997-4d57-9c83-190e83fd6615

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
theorem support_rectangle_w1249_s0_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18584021/100000000 : ℝ)*x 0 + (1507482249/2500000000 : ℝ)*x 1 + (958770779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18584021/100000000 : ℝ)^4221 ≤ (1084039041967/10000000000000 : ℝ)^3197 := by
    have hnat : (18584021 : ℕ)^4221*10000000000000^3197 ≤ 1084039041967^3197*100000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18584021 100000000 1084039041967 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507482249/2500000000 : ℝ)^4221 ≤ (25639888829879/50000000000000 : ℝ)^3197 := by
    have hnat : (1507482249 : ℕ)^4221*50000000000000^3197 ≤ 25639888829879^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507482249 2500000000 25639888829879 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958770779/2000000000 : ℝ)^4221 ≤ (18939915955191/50000000000000 : ℝ)^3197 := by
    have hnat : (958770779 : ℕ)^4221*50000000000000^3197 ≤ 18939915955191^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958770779 2000000000 18939915955191 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18584021/100000000 : ℝ), (1507482249/2500000000 : ℝ), (958770779/2000000000 : ℝ)] ![(1084039041967/10000000000000 : ℝ), (25639888829879/50000000000000 : ℝ), (18939915955191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18584021/100000000 : ℝ)|^4221 ≤ (1084039041967/10000000000000 : ℝ)^3197
        have hw : |(-18584021/100000000 : ℝ)|=(18584021/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1507482249/2500000000 : ℝ)|^4221 ≤ (25639888829879/50000000000000 : ℝ)^3197
        have hw : |(1507482249/2500000000 : ℝ)|=(1507482249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958770779/2000000000 : ℝ)|^4221 ≤ (18939915955191/50000000000000 : ℝ)^3197
        have hw : |(958770779/2000000000 : ℝ)|=(958770779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755382573/5000000000 : ℝ)*x 0 + (-320606031/1250000000 : ℝ)*x 1 + (958770767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755382573/5000000000 : ℝ)^4221 ≤ (22766276543819/50000000000000 : ℝ)^3197 := by
    have hnat : (2755382573 : ℕ)^4221*50000000000000^3197 ≤ 22766276543819^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755382573 5000000000 22766276543819 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320606031/1250000000 : ℝ)^4221 ≤ (103672597561/625000000000 : ℝ)^3197 := by
    have hnat : (320606031 : ℕ)^4221*625000000000^3197 ≤ 103672597561^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320606031 1250000000 103672597561 625000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958770767/2000000000 : ℝ)^4221 ≤ (37879831284421/100000000000000 : ℝ)^3197 := by
    have hnat : (958770767 : ℕ)^4221*100000000000000^3197 ≤ 37879831284421^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958770767 2000000000 37879831284421 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755382573/5000000000 : ℝ), (-320606031/1250000000 : ℝ), (958770767/2000000000 : ℝ)] ![(22766276543819/50000000000000 : ℝ), (103672597561/625000000000 : ℝ), (37879831284421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755382573/5000000000 : ℝ)|^4221 ≤ (22766276543819/50000000000000 : ℝ)^3197
        have hw : |(2755382573/5000000000 : ℝ)|=(2755382573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-320606031/1250000000 : ℝ)|^4221 ≤ (103672597561/625000000000 : ℝ)^3197
        have hw : |(-320606031/1250000000 : ℝ)|=(320606031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958770767/2000000000 : ℝ)|^4221 ≤ (37879831284421/100000000000000 : ℝ)^3197
        have hw : |(958770767/2000000000 : ℝ)|=(958770767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5510765061/10000000000 : ℝ)*x 0 + (4793853927/10000000000 : ℝ)*x 1 + (-641212061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510765061/10000000000 : ℝ)^4221 ≤ (22766276080189/50000000000000 : ℝ)^3197 := by
    have hnat : (5510765061 : ℕ)^4221*50000000000000^3197 ≤ 22766276080189^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510765061 10000000000 22766276080189 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4793853927/10000000000 : ℝ)^4221 ≤ (9469958061057/25000000000000 : ℝ)^3197 := by
    have hnat : (4793853927 : ℕ)^4221*25000000000000^3197 ≤ 9469958061057^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793853927 10000000000 9469958061057 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641212061/2500000000 : ℝ)^4221 ≤ (3317523115121/20000000000000 : ℝ)^3197 := by
    have hnat : (641212061 : ℕ)^4221*20000000000000^3197 ≤ 3317523115121^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641212061 2500000000 3317523115121 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510765061/10000000000 : ℝ), (4793853927/10000000000 : ℝ), (-641212061/2500000000 : ℝ)] ![(22766276080189/50000000000000 : ℝ), (9469958061057/25000000000000 : ℝ), (3317523115121/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510765061/10000000000 : ℝ)|^4221 ≤ (22766276080189/50000000000000 : ℝ)^3197
        have hw : |(5510765061/10000000000 : ℝ)|=(5510765061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4793853927/10000000000 : ℝ)|^4221 ≤ (9469958061057/25000000000000 : ℝ)^3197
        have hw : |(4793853927/10000000000 : ℝ)|=(4793853927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-641212061/2500000000 : ℝ)|^4221 ≤ (3317523115121/20000000000000 : ℝ)^3197
        have hw : |(-641212061/2500000000 : ℝ)|=(641212061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2096236147/5000000000 : ℝ)*x 0 + (779157587/2500000000 : ℝ)*x 1 + (351717833/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096236147/5000000000 : ℝ)^4221 ≤ (31735642882437/100000000000000 : ℝ)^3197 := by
    have hnat : (2096236147 : ℕ)^4221*100000000000000^3197 ≤ 31735642882437^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096236147 5000000000 31735642882437 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779157587/2500000000 : ℝ)^4221 ≤ (21454211259799/100000000000000 : ℝ)^3197 := by
    have hnat : (779157587 : ℕ)^4221*100000000000000^3197 ≤ 21454211259799^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779157587 2500000000 21454211259799 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351717833/625000000 : ℝ)^4221 ≤ (9362029168887/20000000000000 : ℝ)^3197 := by
    have hnat : (351717833 : ℕ)^4221*20000000000000^3197 ≤ 9362029168887^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351717833 625000000 9362029168887 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096236147/5000000000 : ℝ), (779157587/2500000000 : ℝ), (351717833/625000000 : ℝ)] ![(31735642882437/100000000000000 : ℝ), (21454211259799/100000000000000 : ℝ), (9362029168887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096236147/5000000000 : ℝ)|^4221 ≤ (31735642882437/100000000000000 : ℝ)^3197
        have hw : |(2096236147/5000000000 : ℝ)|=(2096236147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779157587/2500000000 : ℝ)|^4221 ≤ (21454211259799/100000000000000 : ℝ)^3197
        have hw : |(779157587/2500000000 : ℝ)|=(779157587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(351717833/625000000 : ℝ)|^4221 ≤ (9362029168887/20000000000000 : ℝ)^3197
        have hw : |(351717833/625000000 : ℝ)|=(351717833/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-93161987/500000000 : ℝ)*x 0 + (1206420231/2500000000 : ℝ)*x 1 + (5996976803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93161987/500000000 : ℝ)^4221 ≤ (10877663252989/100000000000000 : ℝ)^3197 := by
    have hnat : (93161987 : ℕ)^4221*100000000000000^3197 ≤ 10877663252989^3197*500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93161987 500000000 10877663252989 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206420231/2500000000 : ℝ)^4221 ≤ (38212225695519/100000000000000 : ℝ)^3197 := by
    have hnat : (1206420231 : ℕ)^4221*100000000000000^3197 ≤ 38212225695519^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206420231 2500000000 38212225695519 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5996976803/10000000000 : ℝ)^4221 ≤ (6363763878803/12500000000000 : ℝ)^3197 := by
    have hnat : (5996976803 : ℕ)^4221*12500000000000^3197 ≤ 6363763878803^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996976803 10000000000 6363763878803 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93161987/500000000 : ℝ), (1206420231/2500000000 : ℝ), (5996976803/10000000000 : ℝ)] ![(10877663252989/100000000000000 : ℝ), (38212225695519/100000000000000 : ℝ), (6363763878803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93161987/500000000 : ℝ)|^4221 ≤ (10877663252989/100000000000000 : ℝ)^3197
        have hw : |(-93161987/500000000 : ℝ)|=(93161987/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206420231/2500000000 : ℝ)|^4221 ≤ (38212225695519/100000000000000 : ℝ)^3197
        have hw : |(1206420231/2500000000 : ℝ)|=(1206420231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5996976803/10000000000 : ℝ)|^4221 ≤ (6363763878803/12500000000000 : ℝ)^3197
        have hw : |(5996976803/10000000000 : ℝ)|=(5996976803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174417153/10000000000 : ℝ)*x 0 + (-136172307/1000000000 : ℝ)*x 1 + (5996979139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174417153/10000000000 : ℝ)^4221 ≤ (41899725321289/100000000000000 : ℝ)^3197 := by
    have hnat : (5174417153 : ℕ)^4221*100000000000000^3197 ≤ 41899725321289^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174417153 10000000000 41899725321289 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136172307/1000000000 : ℝ)^4221 ≤ (1438027489853/20000000000000 : ℝ)^3197 := by
    have hnat : (136172307 : ℕ)^4221*20000000000000^3197 ≤ 1438027489853^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136172307 1000000000 1438027489853 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5996979139/10000000000 : ℝ)^4221 ≤ (25455068606647/50000000000000 : ℝ)^3197 := by
    have hnat : (5996979139 : ℕ)^4221*50000000000000^3197 ≤ 25455068606647^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996979139 10000000000 25455068606647 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174417153/10000000000 : ℝ), (-136172307/1000000000 : ℝ), (5996979139/10000000000 : ℝ)] ![(41899725321289/100000000000000 : ℝ), (1438027489853/20000000000000 : ℝ), (25455068606647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174417153/10000000000 : ℝ)|^4221 ≤ (41899725321289/100000000000000 : ℝ)^3197
        have hw : |(5174417153/10000000000 : ℝ)|=(5174417153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136172307/1000000000 : ℝ)|^4221 ≤ (1438027489853/20000000000000 : ℝ)^3197
        have hw : |(-136172307/1000000000 : ℝ)|=(136172307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5996979139/10000000000 : ℝ)|^4221 ≤ (25455068606647/50000000000000 : ℝ)^3197
        have hw : |(5996979139/10000000000 : ℝ)|=(5996979139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174418117/10000000000 : ℝ)*x 0 + (5996977239/10000000000 : ℝ)*x 1 + (-1361724647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174418117/10000000000 : ℝ)^4221 ≤ (41899735627511/100000000000000 : ℝ)^3197 := by
    have hnat : (5174418117 : ℕ)^4221*100000000000000^3197 ≤ 41899735627511^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174418117 10000000000 41899735627511 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5996977239/10000000000 : ℝ)^4221 ≤ (10182023183459/20000000000000 : ℝ)^3197 := by
    have hnat : (5996977239 : ℕ)^4221*20000000000000^3197 ≤ 10182023183459^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996977239 10000000000 10182023183459 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361724647/10000000000 : ℝ)^4221 ≤ (7190148443193/100000000000000 : ℝ)^3197 := by
    have hnat : (1361724647 : ℕ)^4221*100000000000000^3197 ≤ 7190148443193^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361724647 10000000000 7190148443193 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174418117/10000000000 : ℝ), (5996977239/10000000000 : ℝ), (-1361724647/10000000000 : ℝ)] ![(41899735627511/100000000000000 : ℝ), (10182023183459/20000000000000 : ℝ), (7190148443193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174418117/10000000000 : ℝ)|^4221 ≤ (41899735627511/100000000000000 : ℝ)^3197
        have hw : |(5174418117/10000000000 : ℝ)|=(5174418117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5996977239/10000000000 : ℝ)|^4221 ≤ (10182023183459/20000000000000 : ℝ)^3197
        have hw : |(5996977239/10000000000 : ℝ)|=(5996977239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1361724647/10000000000 : ℝ)|^4221 ≤ (7190148443193/100000000000000 : ℝ)^3197
        have hw : |(-1361724647/10000000000 : ℝ)|=(1361724647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s0_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2101150289/5000000000 : ℝ)*x 0 + (5562840117/10000000000 : ℝ)*x 1 + (1591780311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101150289/5000000000 : ℝ)^4221 ≤ (6366781195749/20000000000000 : ℝ)^3197 := by
    have hnat : (2101150289 : ℕ)^4221*20000000000000^3197 ≤ 6366781195749^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101150289 5000000000 6366781195749 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5562840117/10000000000 : ℝ)^4221 ≤ (46101494050267/100000000000000 : ℝ)^3197 := by
    have hnat : (5562840117 : ℕ)^4221*100000000000000^3197 ≤ 46101494050267^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562840117 10000000000 46101494050267 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1591780311/5000000000 : ℝ)^4221 ≤ (22064599961203/100000000000000 : ℝ)^3197 := by
    have hnat : (1591780311 : ℕ)^4221*100000000000000^3197 ≤ 22064599961203^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591780311 5000000000 22064599961203 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2101150289/5000000000 : ℝ), (5562840117/10000000000 : ℝ), (1591780311/5000000000 : ℝ)] ![(6366781195749/20000000000000 : ℝ), (46101494050267/100000000000000 : ℝ), (22064599961203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2101150289/5000000000 : ℝ)|^4221 ≤ (6366781195749/20000000000000 : ℝ)^3197
        have hw : |(2101150289/5000000000 : ℝ)|=(2101150289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5562840117/10000000000 : ℝ)|^4221 ≤ (46101494050267/100000000000000 : ℝ)^3197
        have hw : |(5562840117/10000000000 : ℝ)|=(5562840117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1591780311/5000000000 : ℝ)|^4221 ≤ (22064599961203/100000000000000 : ℝ)^3197
        have hw : |(1591780311/5000000000 : ℝ)|=(1591780311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (423/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2741/10000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8441/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8441 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8441*1^2048 ≤ 0^2048*1^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8441/2048 : ℝ) ≤ (17891536595804303/781250000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8441 ≤ (17891536595804303/781250000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8441*781250000000000000^2048 ≤ 17891536595804303^2048*5^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 17891536595804303 781250000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (17891536595804303/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8441 := by
      have hnat : (1 : ℕ)^2048*1^8441 ≤ 1^8441*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (799141536595804303/781250000000000000 : ℝ) ≤ (10055088512194791/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (799141536595804303/781250000000000000 : ℝ)^2048 ≤ (10055088512194791/10000000000000000 : ℝ)^8441 := by
      have hnat : (799141536595804303 : ℕ)^2048*10000000000000000^8441 ≤ 10055088512194791^8441*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        799141536595804303 781250000000000000 10055088512194791 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055088512194791/10000000000000000 : ℝ)) (X := (799141536595804303/781250000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (408516536595804303/390625000000000000 : ℝ) ≤ (5055088512194791/5000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (408516536595804303/390625000000000000 : ℝ)^2048 ≤ (5055088512194791/5000000000000000 : ℝ)^8441 := by
      have hnat : (408516536595804303 : ℕ)^2048*5000000000000000^8441 ≤ 5055088512194791^8441*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        408516536595804303 390625000000000000 5055088512194791 5000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055088512194791/5000000000000000 : ℝ)) (X := (408516536595804303/390625000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55088512194791/4000000000000000 : ℝ)*(0 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55088512194791/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17891536595804303/781250000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55088512194791/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55088512194791/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055088512194791/10000000000000000 : ℝ) by norm_num, show 1+(17891536595804303/781250000000000000 : ℝ)+(0 : ℝ)=(799141536595804303/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17891536595804303/781250000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55088512194791/4000000000000000 : ℝ)*(2/5 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55088512194791/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055088512194791/5000000000000000 : ℝ) by norm_num, show 1+2*(17891536595804303/781250000000000000 : ℝ)=(408516536595804303/390625000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55088512194791/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55088512194791/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55088512194791/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55088512194791/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55088512194791/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55088512194791/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-18584021/100000000 : ℝ)*X 0 0+(1507482249/2500000000 : ℝ)*X 0 1+(958770779/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755382573/5000000000 : ℝ)*X 1 0+(-320606031/1250000000 : ℝ)*X 1 1+(958770767/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510765061/10000000000 : ℝ)*X 2 0+(4793853927/10000000000 : ℝ)*X 2 1+(-641212061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2096236147/5000000000 : ℝ)*X 0 0+(779157587/2500000000 : ℝ)*X 0 1+(351717833/625000000 : ℝ)*X 0 2+(2096236147/5000000000 : ℝ)*X 1 0+(779157587/2500000000 : ℝ)*X 1 1+(351717833/625000000 : ℝ)*X 1 2+(2096236147/5000000000 : ℝ)*X 2 0+(779157587/2500000000 : ℝ)*X 2 1+(351717833/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-93161987/500000000 : ℝ)*X 0 0+(1206420231/2500000000 : ℝ)*X 0 1+(5996976803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174417153/10000000000 : ℝ)*X 1 0+(-136172307/1000000000 : ℝ)*X 1 1+(5996979139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174418117/10000000000 : ℝ)*X 2 0+(5996977239/10000000000 : ℝ)*X 2 1+(-1361724647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2101150289/5000000000 : ℝ)*X 0 0+(5562840117/10000000000 : ℝ)*X 0 1+(1591780311/5000000000 : ℝ)*X 0 2+(2101150289/5000000000 : ℝ)*X 1 0+(5562840117/10000000000 : ℝ)*X 1 1+(1591780311/5000000000 : ℝ)*X 1 2+(2101150289/5000000000 : ℝ)*X 2 0+(5562840117/10000000000 : ℝ)*X 2 1+(1591780311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10204136791748390238261/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10665487/20000000000000 : ℝ)*(base1) + (499399463/50000000000000 : ℝ)*(base19) + (460484861/50000000000000 : ℝ)*(base23) + (65350639/100000000000000 : ℝ)*(base24) + (110526501/50000000000000 : ℝ)*(upper3) + (7545572036943/1250000000000 : ℝ)*(major0) + (7545572036943/1250000000000 : ℝ)*(major1) + (7545572036943/1250000000000 : ℝ)*(major2) + (20225392854857/2500000000000 : ℝ)*(sp0) + (4045084469541/500000000000 : ℝ)*(sp1) + (161803381277353/20000000000000 : ℝ)*(sp2) + (79654345703147/20000000000000 : ℝ)*(sp3) + (55796007/2500000000000 : ℝ)*(sp4) + (857652711/50000000000000 : ℝ)*(sp7) + (24892093571787/6250000000000 : ℝ)*(f.failure) + (404508946353563/50000000000000 : ℝ)*(f.sum) + (2774052148913/2500000000000000000000000000 : ℝ)*base65 + (18908044606087/5000000000000000000000000000 : ℝ)*base68 + (22233094143913/5000000000000000000000000000 : ℝ)*base69 + (8234921866087/5000000000000000000000000000 : ℝ)*base72 + (2264197778913/2500000000000000000000000000 : ℝ)*base73 + (25677913656087/5000000000000000000000000000 : ℝ)*base76 + (28391024191087/5000000000000000000000000000 : ℝ)*base78 + (30987617381087/5000000000000000000000000000 : ℝ)*base80 + (14629369403913/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1883319/625000000000000000000 : ℝ)*base89 + (1883319/625000000000000000000 : ℝ)*base91 + (1883319/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52655385635129969922729/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170523547/100000000000000 : ℝ)*(base1) + (614882991/50000000000000 : ℝ)*(base19) + (55051717/4000000000000 : ℝ)*(base23) + (143221777/50000000000000 : ℝ)*(upper3) + (159256239920427/25000000000000 : ℝ)*(major0) + (159256239920427/25000000000000 : ℝ)*(major1) + (159256239920427/25000000000000 : ℝ)*(major2) + (2518511839/100000000000000 : ℝ)*(sp1) + (232578613/10000000000000 : ℝ)*(sp2) + (51091/78125000000 : ℝ)*(sp3) + (53359592844651/6250000000000 : ℝ)*(sp4) + (853749566713047/100000000000000 : ℝ)*(sp5) + (426874806455907/50000000000000 : ℝ)*(sp6) + (2626851205841/625000000000 : ℝ)*(sp7) + (105074107213647/25000000000000 : ℝ)*(f.failure) + (853753314990869/100000000000000 : ℝ)*(f.sum) + (139304515895757/50000000000000000000000000000 : ℝ)*base65 + (187833069495757/100000000000000000000000000000 : ℝ)*base67 + (922481583095757/100000000000000000000000000000 : ℝ)*base69 + (813609015395757/100000000000000000000000000000 : ℝ)*base71 + (76674153995757/50000000000000000000000000000 : ℝ)*base73 + (895772878095757/100000000000000000000000000000 : ℝ)*base75 + (646401067095757/100000000000000000000000000000 : ℝ)*base77 + (223830297704243/100000000000000000000000000000 : ℝ)*base80 + (327544644795757/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2648139/2500000000000000000000 : ℝ)*base89 + (2648139/2500000000000000000000 : ℝ)*base91 + (2648139/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1249_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (423/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2741/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1249_s1_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055303163/10000000000 : ℝ)*x 0 + (1134770541/2000000000 : ℝ)*x 1 + (5023891181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055303163/10000000000 : ℝ)^4221 ≤ (12381972779269/100000000000000 : ℝ)^3197 := by
    have hnat : (2055303163 : ℕ)^4221*100000000000000^3197 ≤ 12381972779269^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055303163 10000000000 12381972779269 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134770541/2000000000 : ℝ)^4221 ≤ (23660021446199/50000000000000 : ℝ)^3197 := by
    have hnat : (1134770541 : ℕ)^4221*50000000000000^3197 ≤ 23660021446199^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134770541 2000000000 23660021446199 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5023891181/10000000000 : ℝ)^4221 ≤ (10074496077299/25000000000000 : ℝ)^3197 := by
    have hnat : (5023891181 : ℕ)^4221*25000000000000^3197 ≤ 10074496077299^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023891181 10000000000 10074496077299 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055303163/10000000000 : ℝ), (1134770541/2000000000 : ℝ), (5023891181/10000000000 : ℝ)] ![(12381972779269/100000000000000 : ℝ), (23660021446199/50000000000000 : ℝ), (10074496077299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055303163/10000000000 : ℝ)|^4221 ≤ (12381972779269/100000000000000 : ℝ)^3197
        have hw : |(-2055303163/10000000000 : ℝ)|=(2055303163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134770541/2000000000 : ℝ)|^4221 ≤ (23660021446199/50000000000000 : ℝ)^3197
        have hw : |(1134770541/2000000000 : ℝ)|=(1134770541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5023891181/10000000000 : ℝ)|^4221 ≤ (10074496077299/25000000000000 : ℝ)^3197
        have hw : |(5023891181/10000000000 : ℝ)|=(5023891181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706639263/5000000000 : ℝ)*x 0 + (-601052201/2500000000 : ℝ)*x 1 + (627986417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706639263/5000000000 : ℝ)^4221 ≤ (4447210184761/10000000000000 : ℝ)^3197 := by
    have hnat : (2706639263 : ℕ)^4221*10000000000000^3197 ≤ 4447210184761^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706639263 5000000000 4447210184761 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601052201/2500000000 : ℝ)^4221 ≤ (1903739022907/12500000000000 : ℝ)^3197 := by
    have hnat : (601052201 : ℕ)^4221*12500000000000^3197 ≤ 1903739022907^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601052201 2500000000 1903739022907 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627986417/1250000000 : ℝ)^4221 ≤ (40297985950721/100000000000000 : ℝ)^3197 := by
    have hnat : (627986417 : ℕ)^4221*100000000000000^3197 ≤ 40297985950721^3197*1250000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627986417 1250000000 40297985950721 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706639263/5000000000 : ℝ), (-601052201/2500000000 : ℝ), (627986417/1250000000 : ℝ)] ![(4447210184761/10000000000000 : ℝ), (1903739022907/12500000000000 : ℝ), (40297985950721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706639263/5000000000 : ℝ)|^4221 ≤ (4447210184761/10000000000000 : ℝ)^3197
        have hw : |(2706639263/5000000000 : ℝ)|=(2706639263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-601052201/2500000000 : ℝ)|^4221 ≤ (1903739022907/12500000000000 : ℝ)^3197
        have hw : |(-601052201/2500000000 : ℝ)|=(601052201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627986417/1250000000 : ℝ)|^4221 ≤ (40297985950721/100000000000000 : ℝ)^3197
        have hw : |(627986417/1250000000 : ℝ)|=(627986417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706639333/5000000000 : ℝ)*x 0 + (2511945621/5000000000 : ℝ)*x 1 + (-1202104371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706639333/5000000000 : ℝ)^4221 ≤ (11118025841539/25000000000000 : ℝ)^3197 := by
    have hnat : (2706639333 : ℕ)^4221*25000000000000^3197 ≤ 11118025841539^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706639333 5000000000 11118025841539 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2511945621/5000000000 : ℝ)^4221 ≤ (8059596991043/20000000000000 : ℝ)^3197 := by
    have hnat : (2511945621 : ℕ)^4221*20000000000000^3197 ≤ 8059596991043^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511945621 5000000000 8059596991043 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202104371/5000000000 : ℝ)^4221 ≤ (3807477916177/25000000000000 : ℝ)^3197 := by
    have hnat : (1202104371 : ℕ)^4221*25000000000000^3197 ≤ 3807477916177^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202104371 5000000000 3807477916177 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706639333/5000000000 : ℝ), (2511945621/5000000000 : ℝ), (-1202104371/5000000000 : ℝ)] ![(11118025841539/25000000000000 : ℝ), (8059596991043/20000000000000 : ℝ), (3807477916177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706639333/5000000000 : ℝ)|^4221 ≤ (11118025841539/25000000000000 : ℝ)^3197
        have hw : |(2706639333/5000000000 : ℝ)|=(2706639333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2511945621/5000000000 : ℝ)|^4221 ≤ (8059596991043/20000000000000 : ℝ)^3197
        have hw : |(2511945621/5000000000 : ℝ)|=(2511945621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1202104371/5000000000 : ℝ)|^4221 ≤ (3807477916177/25000000000000 : ℝ)^3197
        have hw : |(-1202104371/5000000000 : ℝ)|=(1202104371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215412363/500000000 : ℝ)*x 0 + (115522137/312500000 : ℝ)*x 1 + (2508491957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215412363/500000000 : ℝ)^4221 ≤ (16448905691003/50000000000000 : ℝ)^3197 := by
    have hnat : (215412363 : ℕ)^4221*50000000000000^3197 ≤ 16448905691003^3197*500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215412363 500000000 16448905691003 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115522137/312500000 : ℝ)^4221 ≤ (26877339489573/100000000000000 : ℝ)^3197 := by
    have hnat : (115522137 : ℕ)^4221*100000000000000^3197 ≤ 26877339489573^3197*312500000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115522137 312500000 26877339489573 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508491957/5000000000 : ℝ)^4221 ≤ (40224849119417/100000000000000 : ℝ)^3197 := by
    have hnat : (2508491957 : ℕ)^4221*100000000000000^3197 ≤ 40224849119417^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508491957 5000000000 40224849119417 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215412363/500000000 : ℝ), (115522137/312500000 : ℝ), (2508491957/5000000000 : ℝ)] ![(16448905691003/50000000000000 : ℝ), (26877339489573/100000000000000 : ℝ), (40224849119417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215412363/500000000 : ℝ)|^4221 ≤ (16448905691003/50000000000000 : ℝ)^3197
        have hw : |(215412363/500000000 : ℝ)|=(215412363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(115522137/312500000 : ℝ)|^4221 ≤ (26877339489573/100000000000000 : ℝ)^3197
        have hw : |(115522137/312500000 : ℝ)|=(115522137/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508491957/5000000000 : ℝ)|^4221 ≤ (40224849119417/100000000000000 : ℝ)^3197
        have hw : |(2508491957/5000000000 : ℝ)|=(2508491957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-25699639/125000000 : ℝ)*x 0 + (5032405597/10000000000 : ℝ)*x 1 + (1133035367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25699639/125000000 : ℝ)^4221 ≤ (12387285999007/100000000000000 : ℝ)^3197 := by
    have hnat : (25699639 : ℕ)^4221*100000000000000^3197 ≤ 12387285999007^3197*125000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25699639 125000000 12387285999007 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5032405597/10000000000 : ℝ)^4221 ≤ (40388180562109/100000000000000 : ℝ)^3197 := by
    have hnat : (5032405597 : ℕ)^4221*100000000000000^3197 ≤ 40388180562109^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032405597 10000000000 40388180562109 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133035367/2000000000 : ℝ)^4221 ≤ (47224533425263/100000000000000 : ℝ)^3197 := by
    have hnat : (1133035367 : ℕ)^4221*100000000000000^3197 ≤ 47224533425263^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133035367 2000000000 47224533425263 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25699639/125000000 : ℝ), (5032405597/10000000000 : ℝ), (1133035367/2000000000 : ℝ)] ![(12387285999007/100000000000000 : ℝ), (40388180562109/100000000000000 : ℝ), (47224533425263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25699639/125000000 : ℝ)|^4221 ≤ (12387285999007/100000000000000 : ℝ)^3197
        have hw : |(-25699639/125000000 : ℝ)|=(25699639/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5032405597/10000000000 : ℝ)|^4221 ≤ (40388180562109/100000000000000 : ℝ)^3197
        have hw : |(5032405597/10000000000 : ℝ)|=(5032405597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133035367/2000000000 : ℝ)|^4221 ≤ (47224533425263/100000000000000 : ℝ)^3197
        have hw : |(1133035367/2000000000 : ℝ)|=(1133035367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1049154779/2000000000 : ℝ)*x 0 + (-176292309/1000000000 : ℝ)*x 1 + (1416294271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049154779/2000000000 : ℝ)^4221 ≤ (21332143549881/50000000000000 : ℝ)^3197 := by
    have hnat : (1049154779 : ℕ)^4221*50000000000000^3197 ≤ 21332143549881^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049154779 2000000000 21332143549881 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176292309/1000000000 : ℝ)^4221 ≤ (5055588360251/50000000000000 : ℝ)^3197 := by
    have hnat : (176292309 : ℕ)^4221*50000000000000^3197 ≤ 5055588360251^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176292309 1000000000 5055588360251 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1416294271/2500000000 : ℝ)^4221 ≤ (47224536165741/100000000000000 : ℝ)^3197 := by
    have hnat : (1416294271 : ℕ)^4221*100000000000000^3197 ≤ 47224536165741^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1416294271 2500000000 47224536165741 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049154779/2000000000 : ℝ), (-176292309/1000000000 : ℝ), (1416294271/2500000000 : ℝ)] ![(21332143549881/50000000000000 : ℝ), (5055588360251/50000000000000 : ℝ), (47224536165741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049154779/2000000000 : ℝ)|^4221 ≤ (21332143549881/50000000000000 : ℝ)^3197
        have hw : |(1049154779/2000000000 : ℝ)|=(1049154779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-176292309/1000000000 : ℝ)|^4221 ≤ (5055588360251/50000000000000 : ℝ)^3197
        have hw : |(-176292309/1000000000 : ℝ)|=(176292309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1416294271/2500000000 : ℝ)|^4221 ≤ (47224536165741/100000000000000 : ℝ)^3197
        have hw : |(1416294271/2500000000 : ℝ)|=(1416294271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2622886911/5000000000 : ℝ)*x 0 + (5665176891/10000000000 : ℝ)*x 1 + (-1762923473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622886911/5000000000 : ℝ)^4221 ≤ (42664286315881/100000000000000 : ℝ)^3197 := by
    have hnat : (2622886911 : ℕ)^4221*100000000000000^3197 ≤ 42664286315881^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622886911 5000000000 42664286315881 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5665176891/10000000000 : ℝ)^4221 ≤ (11806133510399/25000000000000 : ℝ)^3197 := by
    have hnat : (5665176891 : ℕ)^4221*25000000000000^3197 ≤ 11806133510399^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665176891 10000000000 11806133510399 25000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1762923473/10000000000 : ℝ)^4221 ≤ (10111179620781/100000000000000 : ℝ)^3197 := by
    have hnat : (1762923473 : ℕ)^4221*100000000000000^3197 ≤ 10111179620781^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1762923473 10000000000 10111179620781 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622886911/5000000000 : ℝ), (5665176891/10000000000 : ℝ), (-1762923473/10000000000 : ℝ)] ![(42664286315881/100000000000000 : ℝ), (11806133510399/25000000000000 : ℝ), (10111179620781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622886911/5000000000 : ℝ)|^4221 ≤ (42664286315881/100000000000000 : ℝ)^3197
        have hw : |(2622886911/5000000000 : ℝ)|=(2622886911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5665176891/10000000000 : ℝ)|^4221 ≤ (11806133510399/25000000000000 : ℝ)^3197
        have hw : |(5665176891/10000000000 : ℝ)|=(5665176891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1762923473/10000000000 : ℝ)|^4221 ≤ (10111179620781/100000000000000 : ℝ)^3197
        have hw : |(-1762923473/10000000000 : ℝ)|=(1762923473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s1_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861920793/2000000000 : ℝ)*x 0 + (4999688599/10000000000 : ℝ)*x 1 + (371433201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861920793/2000000000 : ℝ)^4221 ≤ (16455745066247/50000000000000 : ℝ)^3197 := by
    have hnat : (861920793 : ℕ)^4221*50000000000000^3197 ≤ 16455745066247^3197*2000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861920793 2000000000 16455745066247 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4999688599/10000000000 : ℝ)^4221 ≤ (40041865218391/100000000000000 : ℝ)^3197 := by
    have hnat : (4999688599 : ℕ)^4221*100000000000000^3197 ≤ 40041865218391^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4999688599 10000000000 40041865218391 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371433201/1000000000 : ℝ)^4221 ≤ (27046644638889/100000000000000 : ℝ)^3197 := by
    have hnat : (371433201 : ℕ)^4221*100000000000000^3197 ≤ 27046644638889^3197*1000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371433201 1000000000 27046644638889 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861920793/2000000000 : ℝ), (4999688599/10000000000 : ℝ), (371433201/1000000000 : ℝ)] ![(16455745066247/50000000000000 : ℝ), (40041865218391/100000000000000 : ℝ), (27046644638889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861920793/2000000000 : ℝ)|^4221 ≤ (16455745066247/50000000000000 : ℝ)^3197
        have hw : |(861920793/2000000000 : ℝ)|=(861920793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4999688599/10000000000 : ℝ)|^4221 ≤ (40041865218391/100000000000000 : ℝ)^3197
        have hw : |(4999688599/10000000000 : ℝ)|=(4999688599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(371433201/1000000000 : ℝ)|^4221 ≤ (27046644638889/100000000000000 : ℝ)^3197
        have hw : |(371433201/1000000000 : ℝ)|=(371433201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2741/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1557/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19969/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2741/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (423/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2741/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (423/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2741/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (423/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2741/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (423/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2741/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (423/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2741/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (423/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (423/50000 : ℝ) ^ (8441/2048 : ℝ) ≤ (35842388581/12500000000000000000 : ℝ) := by
    have hpowers : (423/50000 : ℝ)^8441 ≤ (35842388581/12500000000000000000 : ℝ)^2048 := by
      have hnat : (423 : ℕ)^8441*12500000000000000000^2048 ≤ 35842388581^2048*50000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        423 50000 35842388581 12500000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (423/50000 : ℝ)) (X := (35842388581/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2741/10000 : ℝ) ^ (8441/2048 : ℝ) ≤ (482276367278603619/100000000000000000000 : ℝ) := by
    have hpowers : (2741/10000 : ℝ)^8441 ≤ (482276367278603619/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2741 : ℕ)^8441*100000000000000000000^2048 ≤ 482276367278603619^2048*10000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2741 10000 482276367278603619 100000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2741/10000 : ℝ)) (X := (482276367278603619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250000035842388581/6250000000000000000 : ℝ) ≤ (625000000869627/625000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (6250000035842388581/6250000000000000000 : ℝ)^2048 ≤ (625000000869627/625000000000000 : ℝ)^8441 := by
      have hnat : (6250000035842388581 : ℕ)^2048*625000000000000^8441 ≤ 625000000869627^8441*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000035842388581 6250000000000000000 625000000869627 625000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000000869627/625000000000000 : ℝ)) (X := (6250000035842388581/6250000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100482276654017712267/100000000000000000000 : ℝ) ≤ (10011679940824493/10000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (100482276654017712267/100000000000000000000 : ℝ)^2048 ≤ (10011679940824493/10000000000000000 : ℝ)^8441 := by
      have hnat : (100482276654017712267 : ℕ)^2048*10000000000000000^8441 ≤ 10011679940824493^8441*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100482276654017712267 100000000000000000000 10011679940824493 10000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011679940824493/10000000000000000 : ℝ)) (X := (100482276654017712267/100000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50482276367278603619/50000000000000000000 : ℝ) ≤ (5011679933867477/5000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (50482276367278603619/50000000000000000000 : ℝ)^2048 ≤ (5011679933867477/5000000000000000 : ℝ)^8441 := by
      have hnat : (50482276367278603619 : ℕ)^2048*5000000000000000^8441 ≤ 5011679933867477^8441*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50482276367278603619 50000000000000000000 5011679933867477 5000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011679933867477/5000000000000000 : ℝ)) (X := (50482276367278603619/50000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35842388581/12500000000000000000 : ℝ) ≤ ((66405059483319961509/66410000000000000000 : ℝ)+2*(11679926910461/2656400000000000 : ℝ)*(423/50000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (66405059483319961509/66410000000000000000 : ℝ)+2*(11679926910461/2656400000000000 : ℝ)*(423/50000 : ℝ)=(625000000869627/625000000000000 : ℝ) by norm_num, show 1+2*(35842388581/12500000000000000000 : ℝ)=(6250000035842388581/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(482276367278603619/100000000000000000000 : ℝ)+(35842388581/12500000000000000000 : ℝ) ≤ ((66405059483319961509/66410000000000000000 : ℝ)+(11679926910461/2656400000000000 : ℝ)*((2741/10000 : ℝ)+(423/50000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (66405059483319961509/66410000000000000000 : ℝ)+(11679926910461/2656400000000000 : ℝ)*((2741/10000 : ℝ)+(423/50000 : ℝ))=(10011679940824493/10000000000000000 : ℝ) by norm_num, show 1+(482276367278603619/100000000000000000000 : ℝ)+(35842388581/12500000000000000000 : ℝ)=(100482276654017712267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(482276367278603619/100000000000000000000 : ℝ) ≤ ((66405059483319961509/66410000000000000000 : ℝ)+2*(11679926910461/2656400000000000 : ℝ)*(2741/10000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (66405059483319961509/66410000000000000000 : ℝ)+2*(11679926910461/2656400000000000 : ℝ)*(2741/10000 : ℝ)=(5011679933867477/5000000000000000 : ℝ) by norm_num, show 1+2*(482276367278603619/100000000000000000000 : ℝ)=(50482276367278603619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66405059483319961509/66410000000000000000 : ℝ)*(X 1 0+X 2 0)+(11679926910461/2656400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (423/50000 : ℝ)) (hi := (2741/10000 : ℝ)) (c := (66405059483319961509/66410000000000000000 : ℝ)) (alpha := (11679926910461/2656400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66405059483319961509/66410000000000000000 : ℝ)*(X 0 1+X 2 1)+(11679926910461/2656400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (423/50000 : ℝ)) (hi := (2741/10000 : ℝ)) (c := (66405059483319961509/66410000000000000000 : ℝ)) (alpha := (11679926910461/2656400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66405059483319961509/66410000000000000000 : ℝ)*(X 0 2+X 1 2)+(11679926910461/2656400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (423/50000 : ℝ)) (hi := (2741/10000 : ℝ)) (c := (66405059483319961509/66410000000000000000 : ℝ)) (alpha := (11679926910461/2656400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2055303163/10000000000 : ℝ)*X 0 0+(1134770541/2000000000 : ℝ)*X 0 1+(5023891181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706639263/5000000000 : ℝ)*X 1 0+(-601052201/2500000000 : ℝ)*X 1 1+(627986417/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2706639333/5000000000 : ℝ)*X 2 0+(2511945621/5000000000 : ℝ)*X 2 1+(-1202104371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215412363/500000000 : ℝ)*X 0 0+(115522137/312500000 : ℝ)*X 0 1+(2508491957/5000000000 : ℝ)*X 0 2+(215412363/500000000 : ℝ)*X 1 0+(115522137/312500000 : ℝ)*X 1 1+(2508491957/5000000000 : ℝ)*X 1 2+(215412363/500000000 : ℝ)*X 2 0+(115522137/312500000 : ℝ)*X 2 1+(2508491957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-25699639/125000000 : ℝ)*X 0 0+(5032405597/10000000000 : ℝ)*X 0 1+(1133035367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049154779/2000000000 : ℝ)*X 1 0+(-176292309/1000000000 : ℝ)*X 1 1+(1416294271/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2622886911/5000000000 : ℝ)*X 2 0+(5665176891/10000000000 : ℝ)*X 2 1+(-1762923473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861920793/2000000000 : ℝ)*X 0 0+(4999688599/10000000000 : ℝ)*X 0 1+(371433201/1000000000 : ℝ)*X 0 2+(861920793/2000000000 : ℝ)*X 1 0+(4999688599/10000000000 : ℝ)*X 1 1+(371433201/1000000000 : ℝ)*X 1 2+(861920793/2000000000 : ℝ)*X 2 0+(4999688599/10000000000 : ℝ)*X 2 1+(371433201/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (752735541883091896331429967/332050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370331/2000000000000 : ℝ)*(base1) + (133803999/25000000000000 : ℝ)*(base19) + (287503353/50000000000000 : ℝ)*(base23) + (54421147/100000000000000 : ℝ)*(upper3) + (11011801/12500000000000 : ℝ)*(upper5) + (229598033668779/20000000000000 : ℝ)*(major0) + (229598033668779/20000000000000 : ℝ)*(major1) + (229598033668779/20000000000000 : ℝ)*(major2) + (769277806598569/50000000000000 : ℝ)*(sp0) + (384639647675939/25000000000000 : ℝ)*(sp1) + (1538558550913047/100000000000000 : ℝ)*(sp2) + (47338713758439/6250000000000 : ℝ)*(sp3) + (706247833/20000000000000 : ℝ)*(sp4) + (1696551977/100000000000000 : ℝ)*(sp7) + (23669410475111/3125000000000 : ℝ)*(f.failure) + (1538559125919753/100000000000000 : ℝ)*(f.sum) + (26207646161511/5312800000000000000000000000 : ℝ)*base65 + (1138867964735797489/1328200000000000000000000000000000 : ℝ)*base68 + (8625455133619202511/1328200000000000000000000000000000 : ℝ)*base69 + (11726939944994802511/1328200000000000000000000000000000 : ℝ)*base71 + (37925354951741/26564000000000000000000000000 : ℝ)*base74 + (15670659249302602511/1328200000000000000000000000000000 : ℝ)*base75 + (3008885316777602511/1328200000000000000000000000000000 : ℝ)*base77 + (6171983700436402511/1328200000000000000000000000000000 : ℝ)*base79 + (166164602775871/26564000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (514293/312500000000000000000 : ℝ)*base90 + (514293/312500000000000000000 : ℝ)*base92 + (514293/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (478465448730904853055254859/103765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28380449/100000000000000 : ℝ)*(base1) + (86582841/10000000000000 : ℝ)*(base19) + (163590693/20000000000000 : ℝ)*(base23) + (120555443/100000000000000 : ℝ)*(upper3) + (49079389/50000000000000 : ℝ)*(upper5) + (36849125183261/3125000000000 : ℝ)*(major0) + (36849125183261/3125000000000 : ℝ)*(major1) + (36849125183261/3125000000000 : ℝ)*(major2) + (4335641629/100000000000000 : ℝ)*(sp1) + (3525058471/100000000000000 : ℝ)*(sp2) + (790174796751977/50000000000000 : ℝ)*(sp4) + (790172181826733/50000000000000 : ℝ)*(sp5) + (1580345222111569/100000000000000 : ℝ)*(sp6) + (777994264524051/100000000000000 : ℝ)*(sp7) + (1555988585809/200000000000 : ℝ)*(f.failure) + (316069913024701/20000000000000 : ℝ)*(f.sum) + (1135211675893/33205000000000000000000000000 : ℝ)*base65 + (1463951828837657099/207531250000000000000000000000000 : ℝ)*base67 + (510625276983500849/207531250000000000000000000000000 : ℝ)*base69 + (870481758483532099/207531250000000000000000000000000 : ℝ)*base71 + (17051470915497/33205000000000000000000000000 : ℝ)*base74 + (1060024021464188349/207531250000000000000000000000000 : ℝ)*base75 + (1654120281462282099/207531250000000000000000000000000 : ℝ)*base77 + (1470980409426938349/207531250000000000000000000000000 : ℝ)*base79 + (144707993734087/33205000000000000000000000000 : ℝ)*base82 + (154667/20000000000000000000 : ℝ)*base90 + (154667/20000000000000000000 : ℝ)*base92 + (154667/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1249_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2741/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (423/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1557/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19969/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1249_s2_0 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2102998131/10000000000 : ℝ)*x 0 + (1372899397/2500000000 : ℝ)*x 1 + (5175722937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102998131/10000000000 : ℝ)^4221 ≤ (12762742043411/100000000000000 : ℝ)^3197 := by
    have hnat : (2102998131 : ℕ)^4221*100000000000000^3197 ≤ 12762742043411^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102998131 10000000000 12762742043411 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372899397/2500000000 : ℝ)^4221 ≤ (2832723236737/6250000000000 : ℝ)^3197 := by
    have hnat : (1372899397 : ℕ)^4221*6250000000000^3197 ≤ 2832723236737^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372899397 2500000000 2832723236737 6250000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175722937/10000000000 : ℝ)^4221 ≤ (41913686154773/100000000000000 : ℝ)^3197 := by
    have hnat : (5175722937 : ℕ)^4221*100000000000000^3197 ≤ 41913686154773^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175722937 10000000000 41913686154773 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2102998131/10000000000 : ℝ), (1372899397/2500000000 : ℝ), (5175722937/10000000000 : ℝ)] ![(12762742043411/100000000000000 : ℝ), (2832723236737/6250000000000 : ℝ), (41913686154773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2102998131/10000000000 : ℝ)|^4221 ≤ (12762742043411/100000000000000 : ℝ)^3197
        have hw : |(-2102998131/10000000000 : ℝ)|=(2102998131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372899397/2500000000 : ℝ)|^4221 ≤ (2832723236737/6250000000000 : ℝ)^3197
        have hw : |(1372899397/2500000000 : ℝ)|=(1372899397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175722937/10000000000 : ℝ)|^4221 ≤ (41913686154773/100000000000000 : ℝ)^3197
        have hw : |(5175722937/10000000000 : ℝ)|=(5175722937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_1 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684700867/5000000000 : ℝ)*x 0 + (-22665791/100000000 : ℝ)*x 1 + (5054417/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684700867/5000000000 : ℝ)^4221 ≤ (4399679977327/10000000000000 : ℝ)^3197 := by
    have hnat : (2684700867 : ℕ)^4221*10000000000000^3197 ≤ 4399679977327^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684700867 5000000000 4399679977327 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22665791/100000000 : ℝ)^4221 ≤ (14089513294679/100000000000000 : ℝ)^3197 := by
    have hnat : (22665791 : ℕ)^4221*100000000000000^3197 ≤ 14089513294679^3197*100000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22665791 100000000 14089513294679 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5054417/9765625 : ℝ)^4221 ≤ (41913686913903/100000000000000 : ℝ)^3197 := by
    have hnat : (5054417 : ℕ)^4221*100000000000000^3197 ≤ 41913686913903^3197*9765625^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054417 9765625 41913686913903 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684700867/5000000000 : ℝ), (-22665791/100000000 : ℝ), (5054417/9765625 : ℝ)] ![(4399679977327/10000000000000 : ℝ), (14089513294679/100000000000000 : ℝ), (41913686913903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684700867/5000000000 : ℝ)|^4221 ≤ (4399679977327/10000000000000 : ℝ)^3197
        have hw : |(2684700867/5000000000 : ℝ)|=(2684700867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22665791/100000000 : ℝ)|^4221 ≤ (14089513294679/100000000000000 : ℝ)^3197
        have hw : |(-22665791/100000000 : ℝ)|=(22665791/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5054417/9765625 : ℝ)|^4221 ≤ (41913686913903/100000000000000 : ℝ)^3197
        have hw : |(5054417/9765625 : ℝ)|=(5054417/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_2 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369401613/10000000000 : ℝ)*x 0 + (5175723091/10000000000 : ℝ)*x 1 + (-141661197/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369401613/10000000000 : ℝ)^4221 ≤ (43996798464229/100000000000000 : ℝ)^3197 := by
    have hnat : (5369401613 : ℕ)^4221*100000000000000^3197 ≤ 43996798464229^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369401613 10000000000 43996798464229 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175723091/10000000000 : ℝ)^4221 ≤ (5239210975167/12500000000000 : ℝ)^3197 := by
    have hnat : (5175723091 : ℕ)^4221*12500000000000^3197 ≤ 5239210975167^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175723091 10000000000 5239210975167 12500000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141661197/625000000 : ℝ)^4221 ≤ (880594607591/6250000000000 : ℝ)^3197 := by
    have hnat : (141661197 : ℕ)^4221*6250000000000^3197 ≤ 880594607591^3197*625000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141661197 625000000 880594607591 6250000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369401613/10000000000 : ℝ), (5175723091/10000000000 : ℝ), (-141661197/625000000 : ℝ)] ![(43996798464229/100000000000000 : ℝ), (5239210975167/12500000000000 : ℝ), (880594607591/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369401613/10000000000 : ℝ)|^4221 ≤ (43996798464229/100000000000000 : ℝ)^3197
        have hw : |(5369401613/10000000000 : ℝ)|=(5369401613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175723091/10000000000 : ℝ)|^4221 ≤ (5239210975167/12500000000000 : ℝ)^3197
        have hw : |(5175723091/10000000000 : ℝ)|=(5175723091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141661197/625000000 : ℝ)|^4221 ≤ (880594607591/6250000000000 : ℝ)^3197
        have hw : |(-141661197/625000000 : ℝ)|=(141661197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_3 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341206737/10000000000 : ℝ)*x 0 + (4031850859/10000000000 : ℝ)*x 1 + (4673490829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341206737/10000000000 : ℝ)^4221 ≤ (33230509440969/100000000000000 : ℝ)^3197 := by
    have hnat : (4341206737 : ℕ)^4221*100000000000000^3197 ≤ 33230509440969^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341206737 10000000000 33230509440969 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031850859/10000000000 : ℝ)^4221 ≤ (30140289955597/100000000000000 : ℝ)^3197 := by
    have hnat : (4031850859 : ℕ)^4221*100000000000000^3197 ≤ 30140289955597^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031850859 10000000000 30140289955597 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4673490829/10000000000 : ℝ)^4221 ≤ (36629200588887/100000000000000 : ℝ)^3197 := by
    have hnat : (4673490829 : ℕ)^4221*100000000000000^3197 ≤ 36629200588887^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673490829 10000000000 36629200588887 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341206737/10000000000 : ℝ), (4031850859/10000000000 : ℝ), (4673490829/10000000000 : ℝ)] ![(33230509440969/100000000000000 : ℝ), (30140289955597/100000000000000 : ℝ), (36629200588887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341206737/10000000000 : ℝ)|^4221 ≤ (33230509440969/100000000000000 : ℝ)^3197
        have hw : |(4341206737/10000000000 : ℝ)|=(4341206737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031850859/10000000000 : ℝ)|^4221 ≤ (30140289955597/100000000000000 : ℝ)^3197
        have hw : |(4031850859/10000000000 : ℝ)|=(4031850859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4673490829/10000000000 : ℝ)|^4221 ≤ (36629200588887/100000000000000 : ℝ)^3197
        have hw : |(4673490829/10000000000 : ℝ)|=(4673490829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_4 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103075103/10000000000 : ℝ)*x 0 + (5177743711/10000000000 : ℝ)*x 1 + (5489557951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103075103/10000000000 : ℝ)^4221 ≤ (6381679399531/50000000000000 : ℝ)^3197 := by
    have hnat : (2103075103 : ℕ)^4221*50000000000000^3197 ≤ 6381679399531^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103075103 10000000000 6381679399531 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177743711/10000000000 : ℝ)^4221 ≤ (41935293551741/100000000000000 : ℝ)^3197 := by
    have hnat : (5177743711 : ℕ)^4221*100000000000000^3197 ≤ 41935293551741^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177743711 10000000000 41935293551741 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489557951/10000000000 : ℝ)^4221 ≤ (45301347636531/100000000000000 : ℝ)^3197 := by
    have hnat : (5489557951 : ℕ)^4221*100000000000000^3197 ≤ 45301347636531^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489557951 10000000000 45301347636531 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103075103/10000000000 : ℝ), (5177743711/10000000000 : ℝ), (5489557951/10000000000 : ℝ)] ![(6381679399531/50000000000000 : ℝ), (41935293551741/100000000000000 : ℝ), (45301347636531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103075103/10000000000 : ℝ)|^4221 ≤ (6381679399531/50000000000000 : ℝ)^3197
        have hw : |(-2103075103/10000000000 : ℝ)|=(2103075103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177743711/10000000000 : ℝ)|^4221 ≤ (41935293551741/100000000000000 : ℝ)^3197
        have hw : |(5177743711/10000000000 : ℝ)|=(5177743711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489557951/10000000000 : ℝ)|^4221 ≤ (45301347636531/100000000000000 : ℝ)^3197
        have hw : |(5489557951/10000000000 : ℝ)|=(5489557951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_5 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644350367/5000000000 : ℝ)*x 0 + (-488185979/2500000000 : ℝ)*x 1 + (1372389499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644350367/5000000000 : ℝ)^4221 ≤ (21562921487593/50000000000000 : ℝ)^3197 := by
    have hnat : (2644350367 : ℕ)^4221*50000000000000^3197 ≤ 21562921487593^3197*5000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644350367 5000000000 21562921487593 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488185979/2500000000 : ℝ)^4221 ≤ (5786404442249/50000000000000 : ℝ)^3197 := by
    have hnat : (488185979 : ℕ)^4221*50000000000000^3197 ≤ 5786404442249^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488185979 2500000000 5786404442249 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372389499/2500000000 : ℝ)^4221 ≤ (45301348126827/100000000000000 : ℝ)^3197 := by
    have hnat : (1372389499 : ℕ)^4221*100000000000000^3197 ≤ 45301348126827^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372389499 2500000000 45301348126827 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644350367/5000000000 : ℝ), (-488185979/2500000000 : ℝ), (1372389499/2500000000 : ℝ)] ![(21562921487593/50000000000000 : ℝ), (5786404442249/50000000000000 : ℝ), (45301348126827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644350367/5000000000 : ℝ)|^4221 ≤ (21562921487593/50000000000000 : ℝ)^3197
        have hw : |(2644350367/5000000000 : ℝ)|=(2644350367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488185979/2500000000 : ℝ)|^4221 ≤ (5786404442249/50000000000000 : ℝ)^3197
        have hw : |(-488185979/2500000000 : ℝ)|=(488185979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372389499/2500000000 : ℝ)|^4221 ≤ (45301348126827/100000000000000 : ℝ)^3197
        have hw : |(1372389499/2500000000 : ℝ)|=(1372389499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_6 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288700887/10000000000 : ℝ)*x 0 + (5489558089/10000000000 : ℝ)*x 1 + (-78109743/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288700887/10000000000 : ℝ)^4221 ≤ (4312584462241/10000000000000 : ℝ)^3197 := by
    have hnat : (5288700887 : ℕ)^4221*10000000000000^3197 ≤ 4312584462241^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288700887 10000000000 4312584462241 10000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489558089/10000000000 : ℝ)^4221 ≤ (45301349140107/100000000000000 : ℝ)^3197 := by
    have hnat : (5489558089 : ℕ)^4221*100000000000000^3197 ≤ 45301349140107^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489558089 10000000000 45301349140107 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78109743/400000000 : ℝ)^4221 ≤ (2314561243257/20000000000000 : ℝ)^3197 := by
    have hnat : (78109743 : ℕ)^4221*20000000000000^3197 ≤ 2314561243257^3197*400000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78109743 400000000 2314561243257 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288700887/10000000000 : ℝ), (5489558089/10000000000 : ℝ), (-78109743/400000000 : ℝ)] ![(4312584462241/10000000000000 : ℝ), (45301349140107/100000000000000 : ℝ), (2314561243257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288700887/10000000000 : ℝ)|^4221 ≤ (4312584462241/10000000000000 : ℝ)^3197
        have hw : |(5288700887/10000000000 : ℝ)|=(5288700887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489558089/10000000000 : ℝ)|^4221 ≤ (45301349140107/100000000000000 : ℝ)^3197
        have hw : |(5489558089/10000000000 : ℝ)|=(5489558089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78109743/400000000 : ℝ)|^4221 ≤ (2314561243257/20000000000000 : ℝ)^3197
        have hw : |(-78109743/400000000 : ℝ)|=(78109743/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1249_s2_7 (p : ℝ) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4341362583/10000000000 : ℝ)*x 0 + (4669386351/10000000000 : ℝ)*x 1 + (1008998321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341362583/10000000000 : ℝ)^4221 ≤ (16616042251031/50000000000000 : ℝ)^3197 := by
    have hnat : (4341362583 : ℕ)^4221*50000000000000^3197 ≤ 16616042251031^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341362583 10000000000 16616042251031 50000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4669386351/10000000000 : ℝ)^4221 ≤ (7317346639333/20000000000000 : ℝ)^3197 := by
    have hnat : (4669386351 : ℕ)^4221*20000000000000^3197 ≤ 7317346639333^3197*10000000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669386351 10000000000 7317346639333 20000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008998321/2500000000 : ℝ)^4221 ≤ (30181182277833/100000000000000 : ℝ)^3197 := by
    have hnat : (1008998321 : ℕ)^4221*100000000000000^3197 ≤ 30181182277833^3197*2500000000^4221 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008998321 2500000000 30181182277833 100000000000000 4221 3197 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4221/1024 : ℝ)) 4221 3197 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341362583/10000000000 : ℝ), (4669386351/10000000000 : ℝ), (1008998321/2500000000 : ℝ)] ![(16616042251031/50000000000000 : ℝ), (7317346639333/20000000000000 : ℝ), (30181182277833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341362583/10000000000 : ℝ)|^4221 ≤ (16616042251031/50000000000000 : ℝ)^3197
        have hw : |(4341362583/10000000000 : ℝ)|=(4341362583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4669386351/10000000000 : ℝ)|^4221 ≤ (7317346639333/20000000000000 : ℝ)^3197
        have hw : |(4669386351/10000000000 : ℝ)|=(4669386351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008998321/2500000000 : ℝ)|^4221 ≤ (30181182277833/100000000000000 : ℝ)^3197
        have hw : |(1008998321/2500000000 : ℝ)|=(1008998321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1249_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1557/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1191/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3241/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1557/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1557/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1557/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1557/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1557/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1557/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1557/25000 : ℝ) ^ (8441/2048 : ℝ) ≤ (134189607585577/12500000000000000000 : ℝ) := by
    have hpowers : (1557/25000 : ℝ)^8441 ≤ (134189607585577/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1557 : ℕ)^8441*12500000000000000000^2048 ≤ 134189607585577^2048*25000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1557 25000 134189607585577 12500000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1557/25000 : ℝ)) (X := (134189607585577/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19969/100000 : ℝ) ^ (8441/2048 : ℝ) ≤ (65362878860073147/50000000000000000000 : ℝ) := by
    have hpowers : (19969/100000 : ℝ)^8441 ≤ (65362878860073147/50000000000000000000 : ℝ)^2048 := by
      have hnat : (19969 : ℕ)^8441*50000000000000000000^2048 ≤ 65362878860073147^2048*100000^8441 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19969 100000 65362878860073147 50000000000000000000 8441 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19969/100000 : ℝ)) (X := (65362878860073147/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250134189607585577/6250000000000000000 : ℝ) ≤ (500002604602127/500000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (6250134189607585577/6250000000000000000 : ℝ)^2048 ≤ (500002604602127/500000000000000 : ℝ)^8441 := by
      have hnat : (6250134189607585577 : ℕ)^2048*500000000000000^8441 ≤ 500002604602127^8441*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250134189607585577 6250000000000000000 500002604602127 500000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002604602127/500000000000000 : ℝ)) (X := (6250134189607585577/6250000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10013179927458083091/10000000000000000000 : ℝ) ≤ (5001598094401109/5000000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (10013179927458083091/10000000000000000000 : ℝ)^2048 ≤ (5001598094401109/5000000000000000 : ℝ)^8441 := by
      have hnat : (10013179927458083091 : ℕ)^2048*5000000000000000^8441 ≤ 5001598094401109^8441*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10013179927458083091 10000000000000000000 5001598094401109 5000000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001598094401109/5000000000000000 : ℝ)) (X := (10013179927458083091/10000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25065362878860073147/25000000000000000000 : ℝ) ≤ (1250792535695237/1250000000000000 : ℝ) ^ (8441/2048 : ℝ) := by
    have hpowers : (25065362878860073147/25000000000000000000 : ℝ)^2048 ≤ (1250792535695237/1250000000000000 : ℝ)^8441 := by
      have hnat : (25065362878860073147 : ℕ)^2048*1250000000000000^8441 ≤ 1250792535695237^8441*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25065362878860073147 25000000000000000000 1250792535695237 1250000000000000 2048 8441 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250792535695237/1250000000000000 : ℝ)) (X := (25065362878860073147/25000000000000000000 : ℝ)) (by norm_num) 8441 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(134189607585577/12500000000000000000 : ℝ) ≤ ((4906126890268499749/4907500000000000000 : ℝ)+2*(224578339977/98150000000000 : ℝ)*(1557/25000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (4906126890268499749/4907500000000000000 : ℝ)+2*(224578339977/98150000000000 : ℝ)*(1557/25000 : ℝ)=(500002604602127/500000000000000 : ℝ) by norm_num, show 1+2*(134189607585577/12500000000000000000 : ℝ)=(6250134189607585577/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(65362878860073147/50000000000000000000 : ℝ)+(134189607585577/12500000000000000000 : ℝ) ≤ ((4906126890268499749/4907500000000000000 : ℝ)+(224578339977/98150000000000 : ℝ)*((19969/100000 : ℝ)+(1557/25000 : ℝ)))^(8441/2048 : ℝ) := by
    rw [show (4906126890268499749/4907500000000000000 : ℝ)+(224578339977/98150000000000 : ℝ)*((19969/100000 : ℝ)+(1557/25000 : ℝ))=(5001598094401109/5000000000000000 : ℝ) by norm_num, show 1+(65362878860073147/50000000000000000000 : ℝ)+(134189607585577/12500000000000000000 : ℝ)=(10013179927458083091/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(65362878860073147/50000000000000000000 : ℝ) ≤ ((4906126890268499749/4907500000000000000 : ℝ)+2*(224578339977/98150000000000 : ℝ)*(19969/100000 : ℝ))^(8441/2048 : ℝ) := by
    rw [show (4906126890268499749/4907500000000000000 : ℝ)+2*(224578339977/98150000000000 : ℝ)*(19969/100000 : ℝ)=(1250792535695237/1250000000000000 : ℝ) by norm_num, show 1+2*(65362878860073147/50000000000000000000 : ℝ)=(25065362878860073147/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4906126890268499749/4907500000000000000 : ℝ)*(X 1 0+X 2 0)+(224578339977/98150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (1557/25000 : ℝ)) (hi := (19969/100000 : ℝ)) (c := (4906126890268499749/4907500000000000000 : ℝ)) (alpha := (224578339977/98150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4906126890268499749/4907500000000000000 : ℝ)*(X 0 1+X 2 1)+(224578339977/98150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (1557/25000 : ℝ)) (hi := (19969/100000 : ℝ)) (c := (4906126890268499749/4907500000000000000 : ℝ)) (alpha := (224578339977/98150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4906126890268499749/4907500000000000000 : ℝ)*(X 0 2+X 1 2)+(224578339977/98150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8441/2048 : ℝ)) (lo := (1557/25000 : ℝ)) (hi := (19969/100000 : ℝ)) (c := (4906126890268499749/4907500000000000000 : ℝ)) (alpha := (224578339977/98150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2102998131/10000000000 : ℝ)*X 0 0+(1372899397/2500000000 : ℝ)*X 0 1+(5175722937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684700867/5000000000 : ℝ)*X 1 0+(-22665791/100000000 : ℝ)*X 1 1+(5054417/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369401613/10000000000 : ℝ)*X 2 0+(5175723091/10000000000 : ℝ)*X 2 1+(-141661197/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4341206737/10000000000 : ℝ)*X 0 0+(4031850859/10000000000 : ℝ)*X 0 1+(4673490829/10000000000 : ℝ)*X 0 2+(4341206737/10000000000 : ℝ)*X 1 0+(4031850859/10000000000 : ℝ)*X 1 1+(4673490829/10000000000 : ℝ)*X 1 2+(4341206737/10000000000 : ℝ)*X 2 0+(4031850859/10000000000 : ℝ)*X 2 1+(4673490829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2103075103/10000000000 : ℝ)*X 0 0+(5177743711/10000000000 : ℝ)*X 0 1+(5489557951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644350367/5000000000 : ℝ)*X 1 0+(-488185979/2500000000 : ℝ)*X 1 1+(1372389499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288700887/10000000000 : ℝ)*X 2 0+(5489558089/10000000000 : ℝ)*X 2 1+(-78109743/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341362583/10000000000 : ℝ)*X 0 0+(4669386351/10000000000 : ℝ)*X 0 1+(1008998321/2500000000 : ℝ)*X 0 2+(4341362583/10000000000 : ℝ)*X 1 0+(4669386351/10000000000 : ℝ)*X 1 1+(1008998321/2500000000 : ℝ)*X 1 2+(4341362583/10000000000 : ℝ)*X 2 0+(4669386351/10000000000 : ℝ)*X 2 1+(1008998321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1249_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3074272894250058178071/755000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348580561/50000000000000 : ℝ)*(base19) + (291359189/50000000000000 : ℝ)*(base23) + (1157119/5000000000000 : ℝ)*(lower2) + (127870331/100000000000000 : ℝ)*(upper3) + (5067033/12500000000000 : ℝ)*(upper5) + (2362171687647187/100000000000000 : ℝ)*(major0) + (2362171687647187/100000000000000 : ℝ)*(major1) + (2362171687647187/100000000000000 : ℝ)*(major2) + (791455467646809/25000000000000 : ℝ)*(sp0) + (63316570639413/2000000000000 : ℝ)*(sp1) + (1582914323206697/50000000000000 : ℝ)*(sp2) + (19481372855073/1250000000000 : ℝ)*(sp3) + (1471708907/20000000000000 : ℝ)*(sp4) + (1045506817/25000000000000 : ℝ)*(sp7) + (389628502608277/25000000000000 : ℝ)*(f.failure) + (791457307282943/25000000000000 : ℝ)*(f.sum) + (41912413881/755000000000000000000000000 : ℝ)*base65 + (291540105716865851/37750000000000000000000000000000 : ℝ)*base67 + (55670646014865851/37750000000000000000000000000000 : ℝ)*base69 + (52523238443615851/37750000000000000000000000000000 : ℝ)*base71 + (2170127381753/377500000000000000000000000 : ℝ)*base73 + (90204235918384149/37750000000000000000000000000000 : ℝ)*base76 + (17740739236884149/37750000000000000000000000000000 : ℝ)*base78 + (315729976745884149/37750000000000000000000000000000 : ℝ)*base80 + (2374457955863/377500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (10022551/2500000000000000000000 : ℝ)*base90 + (10022551/2500000000000000000000 : ℝ)*base92 + (10022551/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9147977295600100683573/1226875000000000000000000000 : ℝ) := by norm_num
    linear_combination (236354627/12500000000000 : ℝ)*(base19) + (427907313/20000000000000 : ℝ)*(base23) + (33445029/100000000000000 : ℝ)*(upper2) + (1023337/400000000000 : ℝ)*(upper3) + (36468497/25000000000000 : ℝ)*(upper5) + (598229448649323/25000000000000 : ℝ)*(major0) + (598229448649323/25000000000000 : ℝ)*(major1) + (598229448649323/25000000000000 : ℝ)*(major2) + (97415601/500000000000 : ℝ)*(sp1) + (1022284913/4000000000000 : ℝ)*(sp2) + (801758914725289/25000000000000 : ℝ)*(sp4) + (160350714247197/5000000000000 : ℝ)*(sp5) + (1603503981120883/50000000000000 : ℝ)*(sp6) + (315759936349859/20000000000000 : ℝ)*(sp7) + (315759936349859/20000000000000 : ℝ)*(f.failure) + (801758914725289/25000000000000 : ℝ)*(f.sum) + (48718989750787/9815000000000000000000000000 : ℝ)*base66 + (272045526459132427/122687500000000000000000000000000 : ℝ)*base67 + (406262746832569927/122687500000000000000000000000000 : ℝ)*base69 + (1223425096928382427/122687500000000000000000000000000 : ℝ)*base71 + (36498074017007/9815000000000000000000000000 : ℝ)*base74 + (840906542673180073/122687500000000000000000000000000 : ℝ)*base76 + (532169771255430073/122687500000000000000000000000000 : ℝ)*base78 + (506402653208305073/122687500000000000000000000000000 : ℝ)*base80 + (1099991808309/4907500000000000000000000000 : ℝ)*base81 + (5804817/2000000000000000000000 : ℝ)*base90 + (5804817/2000000000000000000000 : ℝ)*base92 + (5804817/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1249_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1557/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1249_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1249_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1249_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1249_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1249_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8441/2048 : ℝ) ≤ p) (hpb : p ≤ (4221/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151565637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1191/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3241/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1249_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
