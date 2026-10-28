-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:20:49.179804+00:00
-- url     : https://prove2.me/submissions/92484bfc-4f9f-4368-8fc5-3d074e1ad568

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
theorem support_rectangle_w1244_s9_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211904631/1000000000 : ℝ)*x 0 + (5391113263/10000000000 : ℝ)*x 1 + (5267285159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211904631/1000000000 : ℝ)^8437 ≤ (6443237424287/50000000000000 : ℝ)^6389 := by
    have hnat : (211904631 : ℕ)^8437*50000000000000^6389 ≤ 6443237424287^6389*1000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211904631 1000000000 6443237424287 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391113263/10000000000 : ℝ)^8437 ≤ (353799910017/800000000000 : ℝ)^6389 := by
    have hnat : (5391113263 : ℕ)^8437*800000000000^6389 ≤ 353799910017^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391113263 10000000000 353799910017 800000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267285159/10000000000 : ℝ)^8437 ≤ (2680533523569/6250000000000 : ℝ)^6389 := by
    have hnat : (5267285159 : ℕ)^8437*6250000000000^6389 ≤ 2680533523569^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267285159 10000000000 2680533523569 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211904631/1000000000 : ℝ), (5391113263/10000000000 : ℝ), (5267285159/10000000000 : ℝ)] ![(6443237424287/50000000000000 : ℝ), (353799910017/800000000000 : ℝ), (2680533523569/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211904631/1000000000 : ℝ)|^8437 ≤ (6443237424287/50000000000000 : ℝ)^6389
        have hw : |(-211904631/1000000000 : ℝ)|=(211904631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391113263/10000000000 : ℝ)|^8437 ≤ (353799910017/800000000000 : ℝ)^6389
        have hw : |(5391113263/10000000000 : ℝ)|=(5391113263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267285159/10000000000 : ℝ)|^8437 ≤ (2680533523569/6250000000000 : ℝ)^6389
        have hw : |(5267285159/10000000000 : ℝ)|=(5267285159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s9_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672143153/5000000000 : ℝ)*x 0 + (-2181829227/10000000000 : ℝ)*x 1 + (131682129/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672143153/5000000000 : ℝ)^8437 ≤ (43718424947667/100000000000000 : ℝ)^6389 := by
    have hnat : (2672143153 : ℕ)^8437*100000000000000^6389 ≤ 43718424947667^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672143153 5000000000 43718424947667 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181829227/10000000000 : ℝ)^8437 ≤ (13393038647733/100000000000000 : ℝ)^6389 := by
    have hnat : (2181829227 : ℕ)^8437*100000000000000^6389 ≤ 13393038647733^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181829227 10000000000 13393038647733 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131682129/250000000 : ℝ)^8437 ≤ (42888536387857/100000000000000 : ℝ)^6389 := by
    have hnat : (131682129 : ℕ)^8437*100000000000000^6389 ≤ 42888536387857^6389*250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131682129 250000000 42888536387857 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672143153/5000000000 : ℝ), (-2181829227/10000000000 : ℝ), (131682129/250000000 : ℝ)] ![(43718424947667/100000000000000 : ℝ), (13393038647733/100000000000000 : ℝ), (42888536387857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672143153/5000000000 : ℝ)|^8437 ≤ (43718424947667/100000000000000 : ℝ)^6389
        have hw : |(2672143153/5000000000 : ℝ)|=(2672143153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181829227/10000000000 : ℝ)|^8437 ≤ (13393038647733/100000000000000 : ℝ)^6389
        have hw : |(-2181829227/10000000000 : ℝ)|=(2181829227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131682129/250000000 : ℝ)|^8437 ≤ (42888536387857/100000000000000 : ℝ)^6389
        have hw : |(131682129/250000000 : ℝ)|=(131682129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s9_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068857261/2000000000 : ℝ)*x 0 + (2633642579/5000000000 : ℝ)*x 1 + (-136364327/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068857261/2000000000 : ℝ)^8437 ≤ (8743684987373/20000000000000 : ℝ)^6389 := by
    have hnat : (1068857261 : ℕ)^8437*20000000000000^6389 ≤ 8743684987373^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068857261 2000000000 8743684987373 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633642579/5000000000 : ℝ)^8437 ≤ (2680533522897/6250000000000 : ℝ)^6389 := by
    have hnat : (2633642579 : ℕ)^8437*6250000000000^6389 ≤ 2680533522897^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633642579 5000000000 2680533522897 6250000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136364327/625000000 : ℝ)^8437 ≤ (1674129836033/12500000000000 : ℝ)^6389 := by
    have hnat : (136364327 : ℕ)^8437*12500000000000^6389 ≤ 1674129836033^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136364327 625000000 1674129836033 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068857261/2000000000 : ℝ), (2633642579/5000000000 : ℝ), (-136364327/625000000 : ℝ)] ![(8743684987373/20000000000000 : ℝ), (2680533522897/6250000000000 : ℝ), (1674129836033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068857261/2000000000 : ℝ)|^8437 ≤ (8743684987373/20000000000000 : ℝ)^6389
        have hw : |(1068857261/2000000000 : ℝ)|=(1068857261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633642579/5000000000 : ℝ)|^8437 ≤ (2680533522897/6250000000000 : ℝ)^6389
        have hw : |(2633642579/5000000000 : ℝ)|=(2633642579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136364327/625000000 : ℝ)|^8437 ≤ (1674129836033/12500000000000 : ℝ)^6389
        have hw : |(-136364327/625000000 : ℝ)|=(136364327/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s9_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350501211/10000000000 : ℝ)*x 0 + (1056654727/2500000000 : ℝ)*x 1 + (2238954981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350501211/10000000000 : ℝ)^8437 ≤ (8329381057943/25000000000000 : ℝ)^6389 := by
    have hnat : (4350501211 : ℕ)^8437*25000000000000^6389 ≤ 8329381057943^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350501211 10000000000 8329381057943 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056654727/2500000000 : ℝ)^8437 ≤ (32070432945949/100000000000000 : ℝ)^6389 := by
    have hnat : (1056654727 : ℕ)^8437*100000000000000^6389 ≤ 32070432945949^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056654727 2500000000 32070432945949 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238954981/5000000000 : ℝ)^8437 ≤ (8653010701533/25000000000000 : ℝ)^6389 := by
    have hnat : (2238954981 : ℕ)^8437*25000000000000^6389 ≤ 8653010701533^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238954981 5000000000 8653010701533 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350501211/10000000000 : ℝ), (1056654727/2500000000 : ℝ), (2238954981/5000000000 : ℝ)] ![(8329381057943/25000000000000 : ℝ), (32070432945949/100000000000000 : ℝ), (8653010701533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350501211/10000000000 : ℝ)|^8437 ≤ (8329381057943/25000000000000 : ℝ)^6389
        have hw : |(4350501211/10000000000 : ℝ)|=(4350501211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056654727/2500000000 : ℝ)|^8437 ≤ (32070432945949/100000000000000 : ℝ)^6389
        have hw : |(1056654727/2500000000 : ℝ)|=(1056654727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238954981/5000000000 : ℝ)|^8437 ≤ (8653010701533/25000000000000 : ℝ)^6389
        have hw : |(2238954981/5000000000 : ℝ)|=(2238954981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s9_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529762739/2500000000 : ℝ)*x 0 + (5267597219/10000000000 : ℝ)*x 1 + (5390800069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529762739/2500000000 : ℝ)^8437 ≤ (12886512158827/100000000000000 : ℝ)^6389 := by
    have hnat : (529762739 : ℕ)^8437*100000000000000^6389 ≤ 12886512158827^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529762739 2500000000 12886512158827 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267597219/10000000000 : ℝ)^8437 ≤ (10722972958731/25000000000000 : ℝ)^6389 := by
    have hnat : (5267597219 : ℕ)^8437*25000000000000^6389 ≤ 10722972958731^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267597219 10000000000 10722972958731 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390800069/10000000000 : ℝ)^8437 ≤ (44221595986763/100000000000000 : ℝ)^6389 := by
    have hnat : (5390800069 : ℕ)^8437*100000000000000^6389 ≤ 44221595986763^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390800069 10000000000 44221595986763 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529762739/2500000000 : ℝ), (5267597219/10000000000 : ℝ), (5390800069/10000000000 : ℝ)] ![(12886512158827/100000000000000 : ℝ), (10722972958731/25000000000000 : ℝ), (44221595986763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529762739/2500000000 : ℝ)|^8437 ≤ (12886512158827/100000000000000 : ℝ)^6389
        have hw : |(-529762739/2500000000 : ℝ)|=(529762739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267597219/10000000000 : ℝ)|^8437 ≤ (10722972958731/25000000000000 : ℝ)^6389
        have hw : |(5267597219/10000000000 : ℝ)|=(5267597219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390800069/10000000000 : ℝ)|^8437 ≤ (44221595986763/100000000000000 : ℝ)^6389
        have hw : |(5390800069/10000000000 : ℝ)|=(5390800069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_s9_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175255313/5000000000 : ℝ)*x 0 + (4477276681/10000000000 : ℝ)*x 1 + (4227254489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175255313/5000000000 : ℝ)^8437 ≤ (33317619447581/100000000000000 : ℝ)^6389 := by
    have hnat : (2175255313 : ℕ)^8437*100000000000000^6389 ≤ 33317619447581^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175255313 5000000000 33317619447581 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4477276681/10000000000 : ℝ)^8437 ≤ (17302789460351/50000000000000 : ℝ)^6389 := by
    have hnat : (4477276681 : ℕ)^8437*50000000000000^6389 ≤ 17302789460351^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477276681 10000000000 17302789460351 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227254489/10000000000 : ℝ)^8437 ≤ (6415360321779/20000000000000 : ℝ)^6389 := by
    have hnat : (4227254489 : ℕ)^8437*20000000000000^6389 ≤ 6415360321779^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227254489 10000000000 6415360321779 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175255313/5000000000 : ℝ), (4477276681/10000000000 : ℝ), (4227254489/10000000000 : ℝ)] ![(33317619447581/100000000000000 : ℝ), (17302789460351/50000000000000 : ℝ), (6415360321779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175255313/5000000000 : ℝ)|^8437 ≤ (33317619447581/100000000000000 : ℝ)^6389
        have hw : |(2175255313/5000000000 : ℝ)|=(2175255313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4477276681/10000000000 : ℝ)|^8437 ≤ (17302789460351/50000000000000 : ℝ)^6389
        have hw : |(4477276681/10000000000 : ℝ)|=(4477276681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227254489/10000000000 : ℝ)|^8437 ≤ (6415360321779/20000000000000 : ℝ)^6389
        have hw : |(4227254489/10000000000 : ℝ)|=(4227254489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5741/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2821/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11481/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11481/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11481/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11481/100000 : ℝ) ^ (2109/512 : ℝ) ≤ (13425308178717369/100000000000000000000 : ℝ) := by
    have hpowers : (11481/100000 : ℝ)^2109 ≤ (13425308178717369/100000000000000000000 : ℝ)^512 := by
      have hnat : (11481 : ℕ)^2109*100000000000000000000^512 ≤ 13425308178717369^512*100000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11481 100000 13425308178717369 100000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11481/100000 : ℝ)) (X := (13425308178717369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (2109/512 : ℝ) ≤ (15671773441259877/50000000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^2109 ≤ (15671773441259877/50000000000000000000 : ℝ)^512 := by
      have hnat : (2821 : ℕ)^2109*50000000000000000000^512 ≤ 15671773441259877^512*20000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 15671773441259877 50000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (15671773441259877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013425308178717369/50000000000000000000 : ℝ) ≤ (5000325891849557/5000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50013425308178717369/50000000000000000000 : ℝ)^512 ≤ (5000325891849557/5000000000000000 : ℝ)^2109 := by
      have hnat : (50013425308178717369 : ℕ)^512*5000000000000000^2109 ≤ 5000325891849557^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013425308178717369 50000000000000000000 5000325891849557 5000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000325891849557/5000000000000000 : ℝ)) (X := (50013425308178717369/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044768855061237123/100000000000000000000 : ℝ) ≤ (625067916576423/625000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (100044768855061237123/100000000000000000000 : ℝ)^512 ≤ (625067916576423/625000000000000 : ℝ)^2109 := by
      have hnat : (100044768855061237123 : ℕ)^512*625000000000000^2109 ≤ 625067916576423^2109*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044768855061237123 100000000000000000000 625067916576423 625000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625067916576423/625000000000000 : ℝ)) (X := (100044768855061237123/100000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015671773441259877/25000000000000000000 : ℝ) ≤ (5000760773373211/5000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25015671773441259877/25000000000000000000 : ℝ)^512 ≤ (5000760773373211/5000000000000000 : ℝ)^2109 := by
      have hnat : (25015671773441259877 : ℕ)^512*5000000000000000^2109 ≤ 5000760773373211^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015671773441259877 25000000000000000000 5000760773373211 5000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000760773373211/5000000000000000 : ℝ)) (X := (25015671773441259877/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13425308178717369/100000000000000000000 : ℝ) ≤ ((6557931132720082997/6560000000000000000 : ℝ)+2*(217440761827/131200000000000 : ℝ)*(11481/100000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (6557931132720082997/6560000000000000000 : ℝ)+2*(217440761827/131200000000000 : ℝ)*(11481/100000 : ℝ)=(5000325891849557/5000000000000000 : ℝ) by norm_num, show 1+2*(13425308178717369/100000000000000000000 : ℝ)=(50013425308178717369/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15671773441259877/50000000000000000000 : ℝ)+(13425308178717369/100000000000000000000 : ℝ) ≤ ((6557931132720082997/6560000000000000000 : ℝ)+(217440761827/131200000000000 : ℝ)*((2821/20000 : ℝ)+(11481/100000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (6557931132720082997/6560000000000000000 : ℝ)+(217440761827/131200000000000 : ℝ)*((2821/20000 : ℝ)+(11481/100000 : ℝ))=(625067916576423/625000000000000 : ℝ) by norm_num, show 1+(15671773441259877/50000000000000000000 : ℝ)+(13425308178717369/100000000000000000000 : ℝ)=(100044768855061237123/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15671773441259877/50000000000000000000 : ℝ) ≤ ((6557931132720082997/6560000000000000000 : ℝ)+2*(217440761827/131200000000000 : ℝ)*(2821/20000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (6557931132720082997/6560000000000000000 : ℝ)+2*(217440761827/131200000000000 : ℝ)*(2821/20000 : ℝ)=(5000760773373211/5000000000000000 : ℝ) by norm_num, show 1+2*(15671773441259877/50000000000000000000 : ℝ)=(25015671773441259877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6557931132720082997/6560000000000000000 : ℝ)*(X 1 0+X 2 0)+(217440761827/131200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (6557931132720082997/6560000000000000000 : ℝ)) (alpha := (217440761827/131200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6557931132720082997/6560000000000000000 : ℝ)*(X 0 1+X 2 1)+(217440761827/131200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (6557931132720082997/6560000000000000000 : ℝ)) (alpha := (217440761827/131200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6557931132720082997/6560000000000000000 : ℝ)*(X 0 2+X 1 2)+(217440761827/131200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (11481/100000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (6557931132720082997/6560000000000000000 : ℝ)) (alpha := (217440761827/131200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211904631/1000000000 : ℝ)*X 0 0+(5391113263/10000000000 : ℝ)*X 0 1+(5267285159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672143153/5000000000 : ℝ)*X 1 0+(-2181829227/10000000000 : ℝ)*X 1 1+(131682129/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068857261/2000000000 : ℝ)*X 2 0+(2633642579/5000000000 : ℝ)*X 2 1+(-136364327/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350501211/10000000000 : ℝ)*X 0 0+(1056654727/2500000000 : ℝ)*X 0 1+(2238954981/5000000000 : ℝ)*X 0 2+(4350501211/10000000000 : ℝ)*X 1 0+(1056654727/2500000000 : ℝ)*X 1 1+(2238954981/5000000000 : ℝ)*X 1 2+(4350501211/10000000000 : ℝ)*X 2 0+(1056654727/2500000000 : ℝ)*X 2 1+(2238954981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529762739/2500000000 : ℝ)*X 0 0+(5267597219/10000000000 : ℝ)*X 0 1+(5390800069/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2175255313/5000000000 : ℝ)*X 0 0+(4477276681/10000000000 : ℝ)*X 0 1+(4227254489/10000000000 : ℝ)*X 0 2+(2175255313/5000000000 : ℝ)*X 1 0+(4477276681/10000000000 : ℝ)*X 1 1+(4227254489/10000000000 : ℝ)*X 1 2+(2175255313/5000000000 : ℝ)*X 2 0+(4477276681/10000000000 : ℝ)*X 2 1+(4227254489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8842759370987285103746361/4000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215766809/50000000000000 : ℝ)*(base19) + (97577821/25000000000000 : ℝ)*(base23) + (10611411/50000000000000 : ℝ)*(lower2) + (31692527/50000000000000 : ℝ)*(upper3) + (6614123/25000000000000 : ℝ)*(upper5) + (3013799148629089/50000000000000 : ℝ)*(major0) + (3013799148629089/50000000000000 : ℝ)*(major1) + (3013799148629089/50000000000000 : ℝ)*(major2) + (8075723835781569/100000000000000 : ℝ)*(sp0) + (4037867436455017/50000000000000 : ℝ)*(sp1) + (8075734914132369/100000000000000 : ℝ)*(sp2) + (3979454748602871/100000000000000 : ℝ)*(sp3) + (2867165521/25000000000000 : ℝ)*(sp4) + (6467780161/100000000000000 : ℝ)*(sp5) + (497432652047879/12500000000000 : ℝ)*(f.failure) + (8075735304443653/100000000000000 : ℝ)*(f.sum) + (3316198997837/3280000000000000000000000000 : ℝ)*base66 + (1624277987072649733/328000000000000000000000000000000 : ℝ)*base67 + (2475501177584649733/328000000000000000000000000000000 : ℝ)*base69 + (325241646359350267/328000000000000000000000000000000 : ℝ)*base72 + (9478451511123/3280000000000000000000000000 : ℝ)*base73 + (8123996664840649733/328000000000000000000000000000000 : ℝ)*base75 + (2138331228607350267/328000000000000000000000000000000 : ℝ)*base78 + (1051890022120649733/328000000000000000000000000000000 : ℝ)*base79 + (18088988670163/3280000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3543729/625000000000000000000 : ℝ)*base90 + (3543729/625000000000000000000 : ℝ)*base92 + (3543729/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1244_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1244_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1244_box_0 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-399083081/2000000000 : ℝ)*x 0 + (5374810959/10000000000 : ℝ)*x 1 + (1343702767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399083081/2000000000 : ℝ)^8437 ≤ (5951526109579/50000000000000 : ℝ)^6389 := by
    have hnat : (399083081 : ℕ)^8437*50000000000000^6389 ≤ 5951526109579^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399083081 2000000000 5951526109579 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374810959/10000000000 : ℝ)^8437 ≤ (44048473294627/100000000000000 : ℝ)^6389 := by
    have hnat : (5374810959 : ℕ)^8437*100000000000000^6389 ≤ 44048473294627^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374810959 10000000000 44048473294627 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343702767/2500000000 : ℝ)^8437 ≤ (22024237237133/50000000000000 : ℝ)^6389 := by
    have hnat : (1343702767 : ℕ)^8437*50000000000000^6389 ≤ 22024237237133^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343702767 2500000000 22024237237133 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399083081/2000000000 : ℝ), (5374810959/10000000000 : ℝ), (1343702767/2500000000 : ℝ)] ![(5951526109579/50000000000000 : ℝ), (44048473294627/100000000000000 : ℝ), (22024237237133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399083081/2000000000 : ℝ)|^8437 ≤ (5951526109579/50000000000000 : ℝ)^6389
        have hw : |(-399083081/2000000000 : ℝ)|=(399083081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374810959/10000000000 : ℝ)|^8437 ≤ (44048473294627/100000000000000 : ℝ)^6389
        have hw : |(5374810959/10000000000 : ℝ)|=(5374810959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343702767/2500000000 : ℝ)|^8437 ≤ (22024237237133/50000000000000 : ℝ)^6389
        have hw : |(1343702767/2500000000 : ℝ)|=(1343702767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_1 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296810711/10000000000 : ℝ)*x 0 + (-525358647/2500000000 : ℝ)*x 1 + (2687405537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296810711/10000000000 : ℝ)^8437 ≤ (1080157370353/2500000000000 : ℝ)^6389 := by
    have hnat : (5296810711 : ℕ)^8437*2500000000000^6389 ≤ 1080157370353^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296810711 10000000000 1080157370353 2500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525358647/2500000000 : ℝ)^8437 ≤ (1274523063249/10000000000000 : ℝ)^6389 := by
    have hnat : (525358647 : ℕ)^8437*10000000000000^6389 ≤ 1274523063249^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525358647 2500000000 1274523063249 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687405537/5000000000 : ℝ)^8437 ≤ (44048474539201/100000000000000 : ℝ)^6389 := by
    have hnat : (2687405537 : ℕ)^8437*100000000000000^6389 ≤ 44048474539201^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687405537 5000000000 44048474539201 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296810711/10000000000 : ℝ), (-525358647/2500000000 : ℝ), (2687405537/5000000000 : ℝ)] ![(1080157370353/2500000000000 : ℝ), (1274523063249/10000000000000 : ℝ), (44048474539201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296810711/10000000000 : ℝ)|^8437 ≤ (1080157370353/2500000000000 : ℝ)^6389
        have hw : |(5296810711/10000000000 : ℝ)|=(5296810711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525358647/2500000000 : ℝ)|^8437 ≤ (1274523063249/10000000000000 : ℝ)^6389
        have hw : |(-525358647/2500000000 : ℝ)|=(525358647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687405537/5000000000 : ℝ)|^8437 ≤ (44048474539201/100000000000000 : ℝ)^6389
        have hw : |(2687405537/5000000000 : ℝ)|=(2687405537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_2 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648405347/5000000000 : ℝ)*x 0 + (134370277/250000000 : ℝ)*x 1 + (-1050717301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648405347/5000000000 : ℝ)^8437 ≤ (43206294630999/100000000000000 : ℝ)^6389 := by
    have hnat : (2648405347 : ℕ)^8437*100000000000000^6389 ≤ 43206294630999^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648405347 5000000000 43206294630999 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134370277/250000000 : ℝ)^8437 ≤ (8809694920827/20000000000000 : ℝ)^6389 := by
    have hnat : (134370277 : ℕ)^8437*20000000000000^6389 ≤ 8809694920827^6389*250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134370277 250000000 8809694920827 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050717301/5000000000 : ℝ)^8437 ≤ (12745230744619/100000000000000 : ℝ)^6389 := by
    have hnat : (1050717301 : ℕ)^8437*100000000000000^6389 ≤ 12745230744619^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050717301 5000000000 12745230744619 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648405347/5000000000 : ℝ), (134370277/250000000 : ℝ), (-1050717301/5000000000 : ℝ)] ![(43206294630999/100000000000000 : ℝ), (8809694920827/20000000000000 : ℝ), (12745230744619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648405347/5000000000 : ℝ)|^8437 ≤ (43206294630999/100000000000000 : ℝ)^6389
        have hw : |(2648405347/5000000000 : ℝ)|=(2648405347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134370277/250000000 : ℝ)|^8437 ≤ (8809694920827/20000000000000 : ℝ)^6389
        have hw : |(134370277/250000000 : ℝ)|=(134370277/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050717301/5000000000 : ℝ)|^8437 ≤ (12745230744619/100000000000000 : ℝ)^6389
        have hw : |(-1050717301/5000000000 : ℝ)|=(1050717301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_3 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2228502549/5000000000 : ℝ)*x 0 + (1074822329/2500000000 : ℝ)*x 1 + (4299289509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2228502549/5000000000 : ℝ)^8437 ≤ (34398822304141/100000000000000 : ℝ)^6389 := by
    have hnat : (2228502549 : ℕ)^8437*100000000000000^6389 ≤ 34398822304141^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228502549 5000000000 34398822304141 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074822329/2500000000 : ℝ)^8437 ≤ (3280058786409/10000000000000 : ℝ)^6389 := by
    have hnat : (1074822329 : ℕ)^8437*10000000000000^6389 ≤ 3280058786409^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074822329 2500000000 3280058786409 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4299289509/10000000000 : ℝ)^8437 ≤ (32800589808543/100000000000000 : ℝ)^6389 := by
    have hnat : (4299289509 : ℕ)^8437*100000000000000^6389 ≤ 32800589808543^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299289509 10000000000 32800589808543 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2228502549/5000000000 : ℝ), (1074822329/2500000000 : ℝ), (4299289509/10000000000 : ℝ)] ![(34398822304141/100000000000000 : ℝ), (3280058786409/10000000000000 : ℝ), (32800589808543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2228502549/5000000000 : ℝ)|^8437 ≤ (34398822304141/100000000000000 : ℝ)^6389
        have hw : |(2228502549/5000000000 : ℝ)|=(2228502549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074822329/2500000000 : ℝ)|^8437 ≤ (3280058786409/10000000000000 : ℝ)^6389
        have hw : |(1074822329/2500000000 : ℝ)|=(1074822329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4299289509/10000000000 : ℝ)|^8437 ≤ (32800589808543/100000000000000 : ℝ)^6389
        have hw : |(4299289509/10000000000 : ℝ)|=(4299289509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_4 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2244051537/10000000000 : ℝ)*x 0 + (2641154041/5000000000 : ℝ)*x 1 + (5158504/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244051537/10000000000 : ℝ)^8437 ≤ (13899711455041/100000000000000 : ℝ)^6389 := by
    have hnat : (2244051537 : ℕ)^8437*100000000000000^6389 ≤ 13899711455041^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244051537 10000000000 13899711455041 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641154041/5000000000 : ℝ)^8437 ≤ (861002883783/2000000000000 : ℝ)^6389 := by
    have hnat : (2641154041 : ℕ)^8437*2000000000000^6389 ≤ 861002883783^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641154041 5000000000 861002883783 2000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5158504/9765625 : ℝ)^8437 ≤ (43050144339823/100000000000000 : ℝ)^6389 := by
    have hnat : (5158504 : ℕ)^8437*100000000000000^6389 ≤ 43050144339823^6389*9765625^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158504 9765625 43050144339823 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2244051537/10000000000 : ℝ), (2641154041/5000000000 : ℝ), (5158504/9765625 : ℝ)] ![(13899711455041/100000000000000 : ℝ), (861002883783/2000000000000 : ℝ), (43050144339823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2244051537/10000000000 : ℝ)|^8437 ≤ (13899711455041/100000000000000 : ℝ)^6389
        have hw : |(-2244051537/10000000000 : ℝ)|=(2244051537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641154041/5000000000 : ℝ)|^8437 ≤ (861002883783/2000000000000 : ℝ)^6389
        have hw : |(2641154041/5000000000 : ℝ)|=(2641154041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5158504/9765625 : ℝ)|^8437 ≤ (43050144339823/100000000000000 : ℝ)^6389
        have hw : |(5158504/9765625 : ℝ)|=(5158504/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_5 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362015831/10000000000 : ℝ)*x 0 + (-2138111943/10000000000 : ℝ)*x 1 + (5282308029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362015831/10000000000 : ℝ)^8437 ≤ (43910052404619/100000000000000 : ℝ)^6389 := by
    have hnat : (5362015831 : ℕ)^8437*100000000000000^6389 ≤ 43910052404619^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362015831 10000000000 43910052404619 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2138111943/10000000000 : ℝ)^8437 ≤ (6519901980643/50000000000000 : ℝ)^6389 := by
    have hnat : (2138111943 : ℕ)^8437*50000000000000^6389 ≤ 6519901980643^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138111943 10000000000 6519901980643 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282308029/10000000000 : ℝ)^8437 ≤ (43050143618747/100000000000000 : ℝ)^6389 := by
    have hnat : (5282308029 : ℕ)^8437*100000000000000^6389 ≤ 43050143618747^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282308029 10000000000 43050143618747 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362015831/10000000000 : ℝ), (-2138111943/10000000000 : ℝ), (5282308029/10000000000 : ℝ)] ![(43910052404619/100000000000000 : ℝ), (6519901980643/50000000000000 : ℝ), (43050143618747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362015831/10000000000 : ℝ)|^8437 ≤ (43910052404619/100000000000000 : ℝ)^6389
        have hw : |(5362015831/10000000000 : ℝ)|=(5362015831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2138111943/10000000000 : ℝ)|^8437 ≤ (6519901980643/50000000000000 : ℝ)^6389
        have hw : |(-2138111943/10000000000 : ℝ)|=(2138111943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282308029/10000000000 : ℝ)|^8437 ≤ (43050143618747/100000000000000 : ℝ)^6389
        have hw : |(5282308029/10000000000 : ℝ)|=(5282308029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_6 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362015799/10000000000 : ℝ)*x 0 + (2641154063/5000000000 : ℝ)*x 1 + (-133631991/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362015799/10000000000 : ℝ)^8437 ≤ (43910052058567/100000000000000 : ℝ)^6389 := by
    have hnat : (5362015799 : ℕ)^8437*100000000000000^6389 ≤ 43910052058567^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362015799 10000000000 43910052058567 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641154063/5000000000 : ℝ)^8437 ≤ (10762536165673/25000000000000 : ℝ)^6389 := by
    have hnat : (2641154063 : ℕ)^8437*25000000000000^6389 ≤ 10762536165673^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641154063 5000000000 10762536165673 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133631991/625000000 : ℝ)^8437 ≤ (6519901630307/50000000000000 : ℝ)^6389 := by
    have hnat : (133631991 : ℕ)^8437*50000000000000^6389 ≤ 6519901630307^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133631991 625000000 6519901630307 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362015799/10000000000 : ℝ), (2641154063/5000000000 : ℝ), (-133631991/625000000 : ℝ)] ![(43910052058567/100000000000000 : ℝ), (10762536165673/25000000000000 : ℝ), (6519901630307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362015799/10000000000 : ℝ)|^8437 ≤ (43910052058567/100000000000000 : ℝ)^6389
        have hw : |(5362015799/10000000000 : ℝ)|=(5362015799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641154063/5000000000 : ℝ)|^8437 ≤ (10762536165673/25000000000000 : ℝ)^6389
        have hw : |(2641154063/5000000000 : ℝ)|=(2641154063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133631991/625000000 : ℝ)|^8437 ≤ (6519901630307/50000000000000 : ℝ)^6389
        have hw : |(-133631991/625000000 : ℝ)|=(133631991/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_7 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4243593909/10000000000 : ℝ)*x 0 + (2202987423/5000000000 : ℝ)*x 1 + (4405975003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243593909/10000000000 : ℝ)^8437 ≤ (4030078939783/12500000000000 : ℝ)^6389 := by
    have hnat : (4243593909 : ℕ)^8437*12500000000000^6389 ≤ 4030078939783^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243593909 10000000000 4030078939783 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202987423/5000000000 : ℝ)^8437 ≤ (16939841718119/50000000000000 : ℝ)^6389 := by
    have hnat : (2202987423 : ℕ)^8437*50000000000000^6389 ≤ 16939841718119^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202987423 5000000000 16939841718119 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405975003/10000000000 : ℝ)^8437 ≤ (4234960628809/12500000000000 : ℝ)^6389 := by
    have hnat : (4405975003 : ℕ)^8437*12500000000000^6389 ≤ 4234960628809^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405975003 10000000000 4234960628809 12500000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243593909/10000000000 : ℝ), (2202987423/5000000000 : ℝ), (4405975003/10000000000 : ℝ)] ![(4030078939783/12500000000000 : ℝ), (16939841718119/50000000000000 : ℝ), (4234960628809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243593909/10000000000 : ℝ)|^8437 ≤ (4030078939783/12500000000000 : ℝ)^6389
        have hw : |(4243593909/10000000000 : ℝ)|=(4243593909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2202987423/5000000000 : ℝ)|^8437 ≤ (16939841718119/50000000000000 : ℝ)^6389
        have hw : |(2202987423/5000000000 : ℝ)|=(2202987423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405975003/10000000000 : ℝ)|^8437 ≤ (4234960628809/12500000000000 : ℝ)^6389
        have hw : |(4405975003/10000000000 : ℝ)|=(4405975003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_8 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191948073/10000000000 : ℝ)*x 0 + (2609603717/5000000000 : ℝ)*x 1 + (5384423843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191948073/10000000000 : ℝ)^8437 ≤ (13475124228851/100000000000000 : ℝ)^6389 := by
    have hnat : (2191948073 : ℕ)^8437*100000000000000^6389 ≤ 13475124228851^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191948073 10000000000 13475124228851 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609603717/5000000000 : ℝ)^8437 ≤ (21186169177563/50000000000000 : ℝ)^6389 := by
    have hnat : (2609603717 : ℕ)^8437*50000000000000^6389 ≤ 21186169177563^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609603717 5000000000 21186169177563 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384423843/10000000000 : ℝ)^8437 ≤ (11038134349883/25000000000000 : ℝ)^6389 := by
    have hnat : (5384423843 : ℕ)^8437*25000000000000^6389 ≤ 11038134349883^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384423843 10000000000 11038134349883 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191948073/10000000000 : ℝ), (2609603717/5000000000 : ℝ), (5384423843/10000000000 : ℝ)] ![(13475124228851/100000000000000 : ℝ), (21186169177563/50000000000000 : ℝ), (11038134349883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191948073/10000000000 : ℝ)|^8437 ≤ (13475124228851/100000000000000 : ℝ)^6389
        have hw : |(-2191948073/10000000000 : ℝ)|=(2191948073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609603717/5000000000 : ℝ)|^8437 ≤ (21186169177563/50000000000000 : ℝ)^6389
        have hw : |(2609603717/5000000000 : ℝ)|=(2609603717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384423843/10000000000 : ℝ)|^8437 ≤ (11038134349883/25000000000000 : ℝ)^6389
        have hw : |(5384423843/10000000000 : ℝ)|=(5384423843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_9 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290031871/10000000000 : ℝ)*x 0 + (-32774313/156250000 : ℝ)*x 1 + (5384423581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290031871/10000000000 : ℝ)^8437 ≤ (43133289579913/100000000000000 : ℝ)^6389 := by
    have hnat : (5290031871 : ℕ)^8437*100000000000000^6389 ≤ 43133289579913^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290031871 10000000000 43133289579913 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32774313/156250000 : ℝ)^8437 ≤ (2542835169797/20000000000000 : ℝ)^6389 := by
    have hnat : (32774313 : ℕ)^8437*20000000000000^6389 ≤ 2542835169797^6389*156250000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32774313 156250000 2542835169797 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384423581/10000000000 : ℝ)^8437 ≤ (44152534562443/100000000000000 : ℝ)^6389 := by
    have hnat : (5384423581 : ℕ)^8437*100000000000000^6389 ≤ 44152534562443^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384423581 10000000000 44152534562443 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290031871/10000000000 : ℝ), (-32774313/156250000 : ℝ), (5384423581/10000000000 : ℝ)] ![(43133289579913/100000000000000 : ℝ), (2542835169797/20000000000000 : ℝ), (44152534562443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290031871/10000000000 : ℝ)|^8437 ≤ (43133289579913/100000000000000 : ℝ)^6389
        have hw : |(5290031871/10000000000 : ℝ)|=(5290031871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32774313/156250000 : ℝ)|^8437 ≤ (2542835169797/20000000000000 : ℝ)^6389
        have hw : |(-32774313/156250000 : ℝ)|=(32774313/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384423581/10000000000 : ℝ)|^8437 ≤ (44152534562443/100000000000000 : ℝ)^6389
        have hw : |(5384423581/10000000000 : ℝ)|=(5384423581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_10 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661253963/1250000000 : ℝ)*x 0 + (1346106003/2500000000 : ℝ)*x 1 + (-2097555673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661253963/1250000000 : ℝ)^8437 ≤ (43133287781763/100000000000000 : ℝ)^6389 := by
    have hnat : (661253963 : ℕ)^8437*100000000000000^6389 ≤ 43133287781763^6389*1250000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661253963 1250000000 43133287781763 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346106003/2500000000 : ℝ)^8437 ≤ (22076269614781/50000000000000 : ℝ)^6389 := by
    have hnat : (1346106003 : ℕ)^8437*50000000000000^6389 ≤ 22076269614781^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346106003 2500000000 22076269614781 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2097555673/10000000000 : ℝ)^8437 ≤ (12714172975399/100000000000000 : ℝ)^6389 := by
    have hnat : (2097555673 : ℕ)^8437*100000000000000^6389 ≤ 12714172975399^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097555673 10000000000 12714172975399 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661253963/1250000000 : ℝ), (1346106003/2500000000 : ℝ), (-2097555673/10000000000 : ℝ)] ![(43133287781763/100000000000000 : ℝ), (22076269614781/50000000000000 : ℝ), (12714172975399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661253963/1250000000 : ℝ)|^8437 ≤ (43133287781763/100000000000000 : ℝ)^6389
        have hw : |(661253963/1250000000 : ℝ)|=(661253963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346106003/2500000000 : ℝ)|^8437 ≤ (22076269614781/50000000000000 : ℝ)^6389
        have hw : |(1346106003/2500000000 : ℝ)|=(1346106003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2097555673/10000000000 : ℝ)|^8437 ≤ (12714172975399/100000000000000 : ℝ)^6389
        have hw : |(-2097555673/10000000000 : ℝ)|=(2097555673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_11 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (447891001/1000000000 : ℝ)*x 0 + (42881963/100000000 : ℝ)*x 1 + (4288196561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447891001/1000000000 : ℝ)^8437 ≤ (17311125435557/50000000000000 : ℝ)^6389 := by
    have hnat : (447891001 : ℕ)^8437*50000000000000^6389 ≤ 17311125435557^6389*1000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447891001 1000000000 17311125435557 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42881963/100000000 : ℝ)^8437 ≤ (32688873243517/100000000000000 : ℝ)^6389 := by
    have hnat : (42881963 : ℕ)^8437*100000000000000^6389 ≤ 32688873243517^6389*100000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42881963 100000000 32688873243517 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4288196561/10000000000 : ℝ)^8437 ≤ (6537775174177/20000000000000 : ℝ)^6389 := by
    have hnat : (4288196561 : ℕ)^8437*20000000000000^6389 ≤ 6537775174177^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288196561 10000000000 6537775174177 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447891001/1000000000 : ℝ), (42881963/100000000 : ℝ), (4288196561/10000000000 : ℝ)] ![(17311125435557/50000000000000 : ℝ), (32688873243517/100000000000000 : ℝ), (6537775174177/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447891001/1000000000 : ℝ)|^8437 ≤ (17311125435557/50000000000000 : ℝ)^6389
        have hw : |(447891001/1000000000 : ℝ)|=(447891001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42881963/100000000 : ℝ)|^8437 ≤ (32688873243517/100000000000000 : ℝ)^6389
        have hw : |(42881963/100000000 : ℝ)|=(42881963/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4288196561/10000000000 : ℝ)|^8437 ≤ (6537775174177/20000000000000 : ℝ)^6389
        have hw : |(4288196561/10000000000 : ℝ)|=(4288196561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_12 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-81911089/400000000 : ℝ)*x 0 + (5436704823/10000000000 : ℝ)*x 1 + (82409813/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81911089/400000000 : ℝ)^8437 ≤ (12317249215001/100000000000000 : ℝ)^6389 := by
    have hnat : (81911089 : ℕ)^8437*100000000000000^6389 ≤ 12317249215001^6389*400000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81911089 400000000 12317249215001 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436704823/10000000000 : ℝ)^8437 ≤ (4471954537081/10000000000000 : ℝ)^6389 := by
    have hnat : (5436704823 : ℕ)^8437*10000000000000^6389 ≤ 4471954537081^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436704823 10000000000 4471954537081 10000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82409813/156250000 : ℝ)^8437 ≤ (8592641080731/20000000000000 : ℝ)^6389 := by
    have hnat : (82409813 : ℕ)^8437*20000000000000^6389 ≤ 8592641080731^6389*156250000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82409813 156250000 8592641080731 20000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81911089/400000000 : ℝ), (5436704823/10000000000 : ℝ), (82409813/156250000 : ℝ)] ![(12317249215001/100000000000000 : ℝ), (4471954537081/10000000000000 : ℝ), (8592641080731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81911089/400000000 : ℝ)|^8437 ≤ (12317249215001/100000000000000 : ℝ)^6389
        have hw : |(-81911089/400000000 : ℝ)|=(81911089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436704823/10000000000 : ℝ)|^8437 ≤ (4471954537081/10000000000000 : ℝ)^6389
        have hw : |(5436704823/10000000000 : ℝ)|=(5436704823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82409813/156250000 : ℝ)|^8437 ≤ (8592641080731/20000000000000 : ℝ)^6389
        have hw : |(82409813/156250000 : ℝ)|=(82409813/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_13 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683855131/5000000000 : ℝ)*x 0 + (-535314547/2500000000 : ℝ)*x 1 + (329639267/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683855131/5000000000 : ℝ)^8437 ≤ (2198582156063/5000000000000 : ℝ)^6389 := by
    have hnat : (2683855131 : ℕ)^8437*5000000000000^6389 ≤ 2198582156063^6389*5000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683855131 5000000000 2198582156063 5000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535314547/2500000000 : ℝ)^8437 ≤ (13065148868339/100000000000000 : ℝ)^6389 := by
    have hnat : (535314547 : ℕ)^8437*100000000000000^6389 ≤ 13065148868339^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535314547 2500000000 13065148868339 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329639267/625000000 : ℝ)^8437 ≤ (21481603992673/50000000000000 : ℝ)^6389 := by
    have hnat : (329639267 : ℕ)^8437*50000000000000^6389 ≤ 21481603992673^6389*625000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329639267 625000000 21481603992673 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683855131/5000000000 : ℝ), (-535314547/2500000000 : ℝ), (329639267/625000000 : ℝ)] ![(2198582156063/5000000000000 : ℝ), (13065148868339/100000000000000 : ℝ), (21481603992673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683855131/5000000000 : ℝ)|^8437 ≤ (2198582156063/5000000000000 : ℝ)^6389
        have hw : |(2683855131/5000000000 : ℝ)|=(2683855131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535314547/2500000000 : ℝ)|^8437 ≤ (13065148868339/100000000000000 : ℝ)^6389
        have hw : |(-535314547/2500000000 : ℝ)|=(535314547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329639267/625000000 : ℝ)|^8437 ≤ (21481603992673/50000000000000 : ℝ)^6389
        have hw : |(329639267/625000000 : ℝ)|=(329639267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_14 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (268385491/500000000 : ℝ)*x 0 + (5274228187/10000000000 : ℝ)*x 1 + (-428251779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268385491/500000000 : ℝ)^8437 ≤ (21985819169897/50000000000000 : ℝ)^6389 := by
    have hnat : (268385491 : ℕ)^8437*50000000000000^6389 ≤ 21985819169897^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268385491 500000000 21985819169897 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274228187/10000000000 : ℝ)^8437 ≤ (42963207070997/100000000000000 : ℝ)^6389 := by
    have hnat : (5274228187 : ℕ)^8437*100000000000000^6389 ≤ 42963207070997^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274228187 10000000000 42963207070997 100000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428251779/2000000000 : ℝ)^8437 ≤ (6532577282497/50000000000000 : ℝ)^6389 := by
    have hnat : (428251779 : ℕ)^8437*50000000000000^6389 ≤ 6532577282497^6389*2000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428251779 2000000000 6532577282497 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268385491/500000000 : ℝ), (5274228187/10000000000 : ℝ), (-428251779/2000000000 : ℝ)] ![(21985819169897/50000000000000 : ℝ), (42963207070997/100000000000000 : ℝ), (6532577282497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268385491/500000000 : ℝ)|^8437 ≤ (21985819169897/50000000000000 : ℝ)^6389
        have hw : |(268385491/500000000 : ℝ)|=(268385491/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274228187/10000000000 : ℝ)|^8437 ≤ (42963207070997/100000000000000 : ℝ)^6389
        have hw : |(5274228187/10000000000 : ℝ)|=(5274228187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428251779/2000000000 : ℝ)|^8437 ≤ (6532577282497/50000000000000 : ℝ)^6389
        have hw : |(-428251779/2000000000 : ℝ)|=(428251779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1244_box_15 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056180287/2500000000 : ℝ)*x 0 + (4415288567/10000000000 : ℝ)*x 1 + (220764431/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056180287/2500000000 : ℝ)^8437 ≤ (8012854698907/25000000000000 : ℝ)^6389 := by
    have hnat : (1056180287 : ℕ)^8437*25000000000000^6389 ≤ 8012854698907^6389*2500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056180287 2500000000 8012854698907 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4415288567/10000000000 : ℝ)^8437 ≤ (16987145162529/50000000000000 : ℝ)^6389 := by
    have hnat : (4415288567 : ℕ)^8437*50000000000000^6389 ≤ 16987145162529^6389*10000000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4415288567 10000000000 16987145162529 50000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220764431/500000000 : ℝ)^8437 ≤ (8493572715901/25000000000000 : ℝ)^6389 := by
    have hnat : (220764431 : ℕ)^8437*25000000000000^6389 ≤ 8493572715901^6389*500000000^8437 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220764431 500000000 8493572715901 25000000000000 8437 6389 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8437/2048 : ℝ)) 8437 6389 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056180287/2500000000 : ℝ), (4415288567/10000000000 : ℝ), (220764431/500000000 : ℝ)] ![(8012854698907/25000000000000 : ℝ), (16987145162529/50000000000000 : ℝ), (8493572715901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056180287/2500000000 : ℝ)|^8437 ≤ (8012854698907/25000000000000 : ℝ)^6389
        have hw : |(1056180287/2500000000 : ℝ)|=(1056180287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4415288567/10000000000 : ℝ)|^8437 ≤ (16987145162529/50000000000000 : ℝ)^6389
        have hw : |(4415288567/10000000000 : ℝ)|=(4415288567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220764431/500000000 : ℝ)|^8437 ≤ (8493572715901/25000000000000 : ℝ)^6389
        have hw : |(220764431/500000000 : ℝ)|=(220764431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1244_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62247/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59379/100000 : ℝ) ∧ (16023/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (1667/2000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5741/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2821/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5741/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2821/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5741/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5741/50000 : ℝ) ^ (2109/512 : ℝ) ≤ (1678765693805503/12500000000000000000 : ℝ) := by
    have hpowers : (5741/50000 : ℝ)^2109 ≤ (1678765693805503/12500000000000000000 : ℝ)^512 := by
      have hnat : (5741 : ℕ)^2109*12500000000000000000^512 ≤ 1678765693805503^512*50000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5741 50000 1678765693805503 12500000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5741/50000 : ℝ)) (X := (1678765693805503/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2821/20000 : ℝ) ^ (2109/512 : ℝ) ≤ (15671773441259877/50000000000000000000 : ℝ) := by
    have hpowers : (2821/20000 : ℝ)^2109 ≤ (15671773441259877/50000000000000000000 : ℝ)^512 := by
      have hnat : (2821 : ℕ)^2109*50000000000000000000^512 ≤ 15671773441259877^512*20000^2109 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2821 20000 15671773441259877 50000000000000000000 2109 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2821/20000 : ℝ)) (X := (15671773441259877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251678765693805503/6250000000000000000 : ℝ) ≤ (2000130403510669/2000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (6251678765693805503/6250000000000000000 : ℝ)^512 ≤ (2000130403510669/2000000000000000 : ℝ)^2109 := by
      have hnat : (6251678765693805503 : ℕ)^512*2000000000000000^2109 ≤ 2000130403510669^2109*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251678765693805503 6250000000000000000 2000130403510669 2000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000130403510669/2000000000000000 : ℝ)) (X := (6251678765693805503/6250000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022386836216481889/50000000000000000000 : ℝ) ≤ (2500271695533507/2500000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (50022386836216481889/50000000000000000000 : ℝ)^512 ≤ (2500271695533507/2500000000000000 : ℝ)^2109 := by
      have hnat : (50022386836216481889 : ℕ)^512*2500000000000000^2109 ≤ 2500271695533507^2109*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022386836216481889 50000000000000000000 2500271695533507 2500000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500271695533507/2500000000000000 : ℝ)) (X := (50022386836216481889/50000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015671773441259877/25000000000000000000 : ℝ) ≤ (10001521546714711/10000000000000000 : ℝ) ^ (2109/512 : ℝ) := by
    have hpowers : (25015671773441259877/25000000000000000000 : ℝ)^512 ≤ (10001521546714711/10000000000000000 : ℝ)^2109 := by
      have hnat : (25015671773441259877 : ℕ)^512*10000000000000000^2109 ≤ 10001521546714711^2109*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015671773441259877 25000000000000000000 10001521546714711 10000000000000000 512 2109 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001521546714711/10000000000000000 : ℝ)) (X := (25015671773441259877/25000000000000000000 : ℝ)) (by norm_num) 2109 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1678765693805503/12500000000000000000 : ℝ) ≤ ((26221726308211619523/26230000000000000000 : ℝ)+2*(434764580683/262300000000000 : ℝ)*(5741/50000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (26221726308211619523/26230000000000000000 : ℝ)+2*(434764580683/262300000000000 : ℝ)*(5741/50000 : ℝ)=(2000130403510669/2000000000000000 : ℝ) by norm_num, show 1+2*(1678765693805503/12500000000000000000 : ℝ)=(6251678765693805503/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15671773441259877/50000000000000000000 : ℝ)+(1678765693805503/12500000000000000000 : ℝ) ≤ ((26221726308211619523/26230000000000000000 : ℝ)+(434764580683/262300000000000 : ℝ)*((2821/20000 : ℝ)+(5741/50000 : ℝ)))^(2109/512 : ℝ) := by
    rw [show (26221726308211619523/26230000000000000000 : ℝ)+(434764580683/262300000000000 : ℝ)*((2821/20000 : ℝ)+(5741/50000 : ℝ))=(2500271695533507/2500000000000000 : ℝ) by norm_num, show 1+(15671773441259877/50000000000000000000 : ℝ)+(1678765693805503/12500000000000000000 : ℝ)=(50022386836216481889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15671773441259877/50000000000000000000 : ℝ) ≤ ((26221726308211619523/26230000000000000000 : ℝ)+2*(434764580683/262300000000000 : ℝ)*(2821/20000 : ℝ))^(2109/512 : ℝ) := by
    rw [show (26221726308211619523/26230000000000000000 : ℝ)+2*(434764580683/262300000000000 : ℝ)*(2821/20000 : ℝ)=(10001521546714711/10000000000000000 : ℝ) by norm_num, show 1+2*(15671773441259877/50000000000000000000 : ℝ)=(25015671773441259877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26221726308211619523/26230000000000000000 : ℝ)*(X 1 0+X 2 0)+(434764580683/262300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (26221726308211619523/26230000000000000000 : ℝ)) (alpha := (434764580683/262300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26221726308211619523/26230000000000000000 : ℝ)*(X 0 1+X 2 1)+(434764580683/262300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (26221726308211619523/26230000000000000000 : ℝ)) (alpha := (434764580683/262300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26221726308211619523/26230000000000000000 : ℝ)*(X 0 2+X 1 2)+(434764580683/262300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2109/512 : ℝ)) (lo := (5741/50000 : ℝ)) (hi := (2821/20000 : ℝ)) (c := (26221726308211619523/26230000000000000000 : ℝ)) (alpha := (434764580683/262300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399083081/2000000000 : ℝ)*X 0 0+(5374810959/10000000000 : ℝ)*X 0 1+(1343702767/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296810711/10000000000 : ℝ)*X 1 0+(-525358647/2500000000 : ℝ)*X 1 1+(2687405537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648405347/5000000000 : ℝ)*X 2 0+(134370277/250000000 : ℝ)*X 2 1+(-1050717301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2228502549/5000000000 : ℝ)*X 0 0+(1074822329/2500000000 : ℝ)*X 0 1+(4299289509/10000000000 : ℝ)*X 0 2+(2228502549/5000000000 : ℝ)*X 1 0+(1074822329/2500000000 : ℝ)*X 1 1+(4299289509/10000000000 : ℝ)*X 1 2+(2228502549/5000000000 : ℝ)*X 2 0+(1074822329/2500000000 : ℝ)*X 2 1+(4299289509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2244051537/10000000000 : ℝ)*X 0 0+(2641154041/5000000000 : ℝ)*X 0 1+(5158504/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5362015831/10000000000 : ℝ)*X 1 0+(-2138111943/10000000000 : ℝ)*X 1 1+(5282308029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362015799/10000000000 : ℝ)*X 2 0+(2641154063/5000000000 : ℝ)*X 2 1+(-133631991/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4243593909/10000000000 : ℝ)*X 0 0+(2202987423/5000000000 : ℝ)*X 0 1+(4405975003/10000000000 : ℝ)*X 0 2+(4243593909/10000000000 : ℝ)*X 1 0+(2202987423/5000000000 : ℝ)*X 1 1+(4405975003/10000000000 : ℝ)*X 1 2+(4243593909/10000000000 : ℝ)*X 2 0+(2202987423/5000000000 : ℝ)*X 2 1+(4405975003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2191948073/10000000000 : ℝ)*X 0 0+(2609603717/5000000000 : ℝ)*X 0 1+(5384423843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290031871/10000000000 : ℝ)*X 1 0+(-32774313/156250000 : ℝ)*X 1 1+(5384423581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((661253963/1250000000 : ℝ)*X 2 0+(1346106003/2500000000 : ℝ)*X 2 1+(-2097555673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((447891001/1000000000 : ℝ)*X 0 0+(42881963/100000000 : ℝ)*X 0 1+(4288196561/10000000000 : ℝ)*X 0 2+(447891001/1000000000 : ℝ)*X 1 0+(42881963/100000000 : ℝ)*X 1 1+(4288196561/10000000000 : ℝ)*X 1 2+(447891001/1000000000 : ℝ)*X 2 0+(42881963/100000000 : ℝ)*X 2 1+(4288196561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-81911089/400000000 : ℝ)*X 0 0+(5436704823/10000000000 : ℝ)*X 0 1+(82409813/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2683855131/5000000000 : ℝ)*X 1 0+(-535314547/2500000000 : ℝ)*X 1 1+(329639267/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((268385491/500000000 : ℝ)*X 2 0+(5274228187/10000000000 : ℝ)*X 2 1+(-428251779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1056180287/2500000000 : ℝ)*X 0 0+(4415288567/10000000000 : ℝ)*X 0 1+(220764431/500000000 : ℝ)*X 0 2+(1056180287/2500000000 : ℝ)*X 1 0+(4415288567/10000000000 : ℝ)*X 1 1+(220764431/500000000 : ℝ)*X 1 2+(1056180287/2500000000 : ℝ)*X 2 0+(4415288567/10000000000 : ℝ)*X 2 1+(220764431/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1244_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62247/100000 : ℝ) ≤ (-204084108441223756806887848678779/327875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47461119/50000000000000 : ℝ)*(upper0) + (45937071/50000000000000 : ℝ)*(upper1) + (57216719/100000000000000 : ℝ)*(upper3) + (1328483/1000000000000 : ℝ)*(upper5) + (2002475045478909/50000000000000 : ℝ)*(major0) + (2002475045478909/50000000000000 : ℝ)*(major1) + (2002475045478909/50000000000000 : ℝ)*(major2) + (1321749763/50000000000000 : ℝ)*(sp1) + (6763196303/100000000000000 : ℝ)*(sp3) + (2693275458439891/50000000000000 : ℝ)*(sp4) + (2693275263876261/50000000000000 : ℝ)*(sp5) + (5386553171252047/100000000000000 : ℝ)*(sp6) + (330511051183011/12500000000000 : ℝ)*(sp7) + (450874453/20000000000000 : ℝ)*(sp8) + (264409517266039/10000000000000 : ℝ)*(f.failure) + (5386553171252047/100000000000000 : ℝ)*(f.sum) + (22894298988111/13115000000000000000000000000 : ℝ)*base66 + (22209430003218840407/1311500000000000000000000000000000 : ℝ)*base67 + (21845247321903159593/1311500000000000000000000000000000 : ℝ)*base70 + (14658600438407159593/1311500000000000000000000000000000 : ℝ)*base72 + (81555426911859/3278750000000000000000000000 : ℝ)*base74 + (48813517682245659593/1311500000000000000000000000000000 : ℝ)*base76 + (10685662714434659593/1311500000000000000000000000000000 : ℝ)*base78 + (69975666025743159593/1311500000000000000000000000000000 : ℝ)*base80 + (27065511812909/13115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (454111/500000000000000000000 : ℝ)*base89 + (454111/500000000000000000000 : ℝ)*base91 + (454111/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59379/100000 : ℝ) ≤ (155757640562243811196805530368927/262300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15296989/50000000000000 : ℝ)*(lower1) + (22054147/100000000000000 : ℝ)*(upper2) + (10438429/50000000000000 : ℝ)*(upper5) + (814155767873383/20000000000000 : ℝ)*(major0) + (814155767873383/20000000000000 : ℝ)*(major1) + (814155767873383/20000000000000 : ℝ)*(major2) + (5434202528174319/100000000000000 : ℝ)*(sp0) + (2717102498546893/50000000000000 : ℝ)*(sp1) + (5434206962582339/100000000000000 : ℝ)*(sp2) + (671888866012603/25000000000000 : ℝ)*(sp3) + (3094449303/100000000000000 : ℝ)*(sp5) + (1128960749/100000000000000 : ℝ)*(sp6) + (36764979/12500000000000 : ℝ)*(sp7) + (556336877/10000000000000 : ℝ)*(sp12) + (671888939542561/25000000000000 : ℝ)*(f.failure) + (339638005721443/6250000000000 : ℝ)*(f.sum) + (67551524769/327875000000000000000000000 : ℝ)*base65 + (1603967907696756309/524600000000000000000000000000000 : ℝ)*base67 + (2354048253091843691/524600000000000000000000000000000 : ℝ)*base70 + (3667096225460043691/524600000000000000000000000000000 : ℝ)*base72 + (5838756254637/655750000000000000000000000 : ℝ)*base73 + (5867722851419243691/524600000000000000000000000000000 : ℝ)*base76 + (94753351778843691/524600000000000000000000000000000 : ℝ)*base78 + (1899253253766956309/524600000000000000000000000000000 : ℝ)*base79 + (16060546311197/2623000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6347289/1250000000000000000000 : ℝ)*base89 + (6347289/1250000000000000000000 : ℝ)*base91 + (6347289/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16023/20000 : ℝ) ≤ (1050738298649929071134298650571717/1311500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241006529/100000000000000 : ℝ)*(lower3) + (4962451/10000000000000 : ℝ)*(upper4) + (6352603/20000000000000 : ℝ)*(lower5) + (4537561422906431/100000000000000 : ℝ)*(major0) + (4537561422906431/100000000000000 : ℝ)*(major1) + (4537561422906431/100000000000000 : ℝ)*(major2) + (5462505059/50000000000000 : ℝ)*(sp0) + (96674116273/100000000000000 : ℝ)*(sp1) + (318982977217/100000000000000 : ℝ)*(sp2) + (129817682359/100000000000000 : ℝ)*(sp3) + (6052677375443631/100000000000000 : ℝ)*(sp8) + (6052591626337477/100000000000000 : ℝ)*(sp9) + (6052369317476533/100000000000000 : ℝ)*(sp10) + (149779948165957/5000000000000 : ℝ)*(sp11) + (1497864390500749/50000000000000 : ℝ)*(f.failure) + (4842150640363/80000000000 : ℝ)*(f.sum) + (28736432164231/6557500000000000000000000000 : ℝ)*base66 + (7999322553140847587/2623000000000000000000000000000000 : ℝ)*base68 + (14375926749604847587/2623000000000000000000000000000000 : ℝ)*base70 + (11737078384256847587/2623000000000000000000000000000000 : ℝ)*base72 + (65119957571067/13115000000000000000000000000 : ℝ)*base74 + (28565235107590847587/2623000000000000000000000000000000 : ℝ)*base76 + (12241825579236847587/2623000000000000000000000000000000 : ℝ)*base78 + (22361398368160847587/2623000000000000000000000000000000 : ℝ)*base80 + (25563389958347/13115000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (15847099/2500000000000000000000 : ℝ)*base90 + (15847099/2500000000000000000000 : ℝ)*base92 + (15847099/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-1667/2000 : ℝ) ≤ (-54655180300731024613268953170393/65575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5709207/1000000000000 : ℝ)*(lower0) + (38273013/12500000000000 : ℝ)*(lower1) + (27567081/5000000000000 : ℝ)*(lower4) + (457306186461897/10000000000000 : ℝ)*(major0) + (457306186461897/10000000000000 : ℝ)*(major1) + (457306186461897/10000000000000 : ℝ)*(major2) + (2440988541/25000000000000 : ℝ)*(sp0) + (158840892729/50000000000000 : ℝ)*(sp5) + (404111453051/50000000000000 : ℝ)*(sp6) + (143173952329/100000000000000 : ℝ)*(sp7) + (6154730081308773/100000000000000 : ℝ)*(sp12) + (6154422163477479/100000000000000 : ℝ)*(sp13) + (1538482905589209/25000000000000 : ℝ)*(sp14) + (3019023239086423/100000000000000 : ℝ)*(sp15) + (94348950407461/3125000000000 : ℝ)*(f.failure) + (6154739845262937/100000000000000 : ℝ)*(f.sum) + (2961158363029/1311500000000000000000000000 : ℝ)*base66 + (3761777564916915131/262300000000000000000000000000000 : ℝ)*base67 + (2759814514855415131/262300000000000000000000000000000 : ℝ)*base69 + (3016589788055615131/262300000000000000000000000000000 : ℝ)*base71 + (64687882423273/524600000000000000000000000 : ℝ)*base74 + (2888363369166815131/262300000000000000000000000000000 : ℝ)*base75 + (2758733170515015131/262300000000000000000000000000000 : ℝ)*base77 + (36519823793799784869/262300000000000000000000000000000 : ℝ)*base80 + (6145869167857/2623000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (777611/156250000000000000000 : ℝ)*base90 + (777611/156250000000000000000 : ℝ)*base92 + (777611/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1244_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5741/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59379/100000 : ℝ) else (16023/20000 : ℝ) ≤ X j i ∧ X j i ≤ (1667/2000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1244_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1244_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59379/100000 : ℝ) else (16023/20000 : ℝ) ≤ X j i ∧ X j i ≤ (1667/2000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1244_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1244_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75733849/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2821/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11481/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59379/100000 : ℝ) else (16023/20000 : ℝ) ≤ X j i ∧ X j i ≤ (1667/2000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1244_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
