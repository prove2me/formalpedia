-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1424_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:14.989667+00:00
-- url     : https://prove2.me/submissions/44ca1201-267c-4eff-96dc-fb9ace7e00aa

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
theorem support_rectangle_w1424_s3_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-987053459/5000000000 : ℝ)*x 0 + (338611969/625000000 : ℝ)*x 1 + (1309548789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987053459/5000000000 : ℝ)^137 ≤ (12040000191059/100000000000000 : ℝ)^105 := by
    have hnat : (987053459 : ℕ)^137*100000000000000^105 ≤ 12040000191059^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987053459 5000000000 12040000191059 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338611969/625000000 : ℝ)^137 ≤ (11236769439127/25000000000000 : ℝ)^105 := by
    have hnat : (338611969 : ℕ)^137*25000000000000^105 ≤ 11236769439127^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338611969 625000000 11236769439127 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309548789/2500000000 : ℝ)^137 ≤ (43012922036009/100000000000000 : ℝ)^105 := by
    have hnat : (1309548789 : ℕ)^137*100000000000000^105 ≤ 43012922036009^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309548789 2500000000 43012922036009 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987053459/5000000000 : ℝ), (338611969/625000000 : ℝ), (1309548789/2500000000 : ℝ)] ![(12040000191059/100000000000000 : ℝ), (11236769439127/25000000000000 : ℝ), (43012922036009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987053459/5000000000 : ℝ)|^137 ≤ (12040000191059/100000000000000 : ℝ)^105
        have hw : |(-987053459/5000000000 : ℝ)|=(987053459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338611969/625000000 : ℝ)|^137 ≤ (11236769439127/25000000000000 : ℝ)^105
        have hw : |(338611969/625000000 : ℝ)|=(338611969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309548789/2500000000 : ℝ)|^137 ≤ (43012922036009/100000000000000 : ℝ)^105
        have hw : |(1309548789/2500000000 : ℝ)|=(1309548789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (668729373/1250000000 : ℝ)*x 0 + (-2065727477/10000000000 : ℝ)*x 1 + (2619097563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668729373/1250000000 : ℝ)^137 ≤ (44212888102649/100000000000000 : ℝ)^105 := by
    have hnat : (668729373 : ℕ)^137*100000000000000^105 ≤ 44212888102649^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668729373 1250000000 44212888102649 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065727477/10000000000 : ℝ)^137 ≤ (6387095083393/50000000000000 : ℝ)^105 := by
    have hnat : (2065727477 : ℕ)^137*50000000000000^105 ≤ 6387095083393^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065727477 10000000000 6387095083393 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619097563/5000000000 : ℝ)^137 ≤ (43012921714591/100000000000000 : ℝ)^105 := by
    have hnat : (2619097563 : ℕ)^137*100000000000000^105 ≤ 43012921714591^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619097563 5000000000 43012921714591 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668729373/1250000000 : ℝ), (-2065727477/10000000000 : ℝ), (2619097563/5000000000 : ℝ)] ![(44212888102649/100000000000000 : ℝ), (6387095083393/50000000000000 : ℝ), (43012921714591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668729373/1250000000 : ℝ)|^137 ≤ (44212888102649/100000000000000 : ℝ)^105
        have hw : |(668729373/1250000000 : ℝ)|=(668729373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065727477/10000000000 : ℝ)|^137 ≤ (6387095083393/50000000000000 : ℝ)^105
        have hw : |(-2065727477/10000000000 : ℝ)|=(2065727477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619097563/5000000000 : ℝ)|^137 ≤ (43012921714591/100000000000000 : ℝ)^105
        have hw : |(2619097563/5000000000 : ℝ)|=(2619097563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1069967/2000000 : ℝ)*x 0 + (5238195123/10000000000 : ℝ)*x 1 + (-103286373/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069967/2000000 : ℝ)^137 ≤ (44212888275177/100000000000000 : ℝ)^105 := by
    have hnat : (1069967 : ℕ)^137*100000000000000^105 ≤ 44212888275177^105*2000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069967 2000000 44212888275177 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238195123/10000000000 : ℝ)^137 ≤ (43012921682449/100000000000000 : ℝ)^105 := by
    have hnat : (5238195123 : ℕ)^137*100000000000000^105 ≤ 43012921682449^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238195123 10000000000 43012921682449 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103286373/500000000 : ℝ)^137 ≤ (6387095014811/50000000000000 : ℝ)^105 := by
    have hnat : (103286373 : ℕ)^137*50000000000000^105 ≤ 6387095014811^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103286373 500000000 6387095014811 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069967/2000000 : ℝ), (5238195123/10000000000 : ℝ), (-103286373/500000000 : ℝ)] ![(44212888275177/100000000000000 : ℝ), (43012921682449/100000000000000 : ℝ), (6387095014811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069967/2000000 : ℝ)|^137 ≤ (44212888275177/100000000000000 : ℝ)^105
        have hw : |(1069967/2000000 : ℝ)|=(1069967/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238195123/10000000000 : ℝ)|^137 ≤ (43012921682449/100000000000000 : ℝ)^105
        have hw : |(5238195123/10000000000 : ℝ)|=(5238195123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103286373/500000000 : ℝ)|^137 ≤ (6387095014811/50000000000000 : ℝ)^105
        have hw : |(-103286373/500000000 : ℝ)|=(103286373/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2152480139/5000000000 : ℝ)*x 0 + (4114987827/10000000000 : ℝ)*x 1 + (4502802999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152480139/5000000000 : ℝ)^137 ≤ (33297903401961/100000000000000 : ℝ)^105 := by
    have hnat : (2152480139 : ℕ)^137*100000000000000^105 ≤ 33297903401961^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152480139 5000000000 33297903401961 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114987827/10000000000 : ℝ)^137 ≤ (15696860020077/50000000000000 : ℝ)^105 := by
    have hnat : (4114987827 : ℕ)^137*50000000000000^105 ≤ 15696860020077^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114987827 10000000000 15696860020077 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502802999/10000000000 : ℝ)^137 ≤ (35308376545471/100000000000000 : ℝ)^105 := by
    have hnat : (4502802999 : ℕ)^137*100000000000000^105 ≤ 35308376545471^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502802999 10000000000 35308376545471 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152480139/5000000000 : ℝ), (4114987827/10000000000 : ℝ), (4502802999/10000000000 : ℝ)] ![(33297903401961/100000000000000 : ℝ), (15696860020077/50000000000000 : ℝ), (35308376545471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152480139/5000000000 : ℝ)|^137 ≤ (33297903401961/100000000000000 : ℝ)^105
        have hw : |(2152480139/5000000000 : ℝ)|=(2152480139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4114987827/10000000000 : ℝ)|^137 ≤ (15696860020077/50000000000000 : ℝ)^105
        have hw : |(4114987827/10000000000 : ℝ)|=(4114987827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502802999/10000000000 : ℝ)|^137 ≤ (35308376545471/100000000000000 : ℝ)^105
        have hw : |(4502802999/10000000000 : ℝ)|=(4502802999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-987061117/5000000000 : ℝ)*x 0 + (654864237/1250000000 : ℝ)*x 1 + (5417068821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987061117/5000000000 : ℝ)^137 ≤ (2408024414241/20000000000000 : ℝ)^105 := by
    have hnat : (987061117 : ℕ)^137*20000000000000^105 ≤ 2408024414241^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987061117 5000000000 2408024414241 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654864237/1250000000 : ℝ)^137 ≤ (43020622722373/100000000000000 : ℝ)^105 := by
    have hnat : (654864237 : ℕ)^137*100000000000000^105 ≤ 43020622722373^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654864237 1250000000 43020622722373 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417068821/10000000000 : ℝ)^137 ≤ (11234813796653/25000000000000 : ℝ)^105 := by
    have hnat : (5417068821 : ℕ)^137*25000000000000^105 ≤ 11234813796653^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417068821 10000000000 11234813796653 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987061117/5000000000 : ℝ), (654864237/1250000000 : ℝ), (5417068821/10000000000 : ℝ)] ![(2408024414241/20000000000000 : ℝ), (43020622722373/100000000000000 : ℝ), (11234813796653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987061117/5000000000 : ℝ)|^137 ≤ (2408024414241/20000000000000 : ℝ)^105
        have hw : |(-987061117/5000000000 : ℝ)|=(987061117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654864237/1250000000 : ℝ)|^137 ≤ (43020622722373/100000000000000 : ℝ)^105
        have hw : |(654864237/1250000000 : ℝ)|=(654864237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417068821/10000000000 : ℝ)|^137 ≤ (11234813796653/25000000000000 : ℝ)^105
        have hw : |(5417068821/10000000000 : ℝ)|=(5417068821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2651584221/5000000000 : ℝ)*x 0 + (-1886853807/10000000000 : ℝ)*x 1 + (1083413763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651584221/5000000000 : ℝ)^137 ≤ (21855176409779/50000000000000 : ℝ)^105 := by
    have hnat : (2651584221 : ℕ)^137*50000000000000^105 ≤ 21855176409779^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651584221 5000000000 21855176409779 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1886853807/10000000000 : ℝ)^137 ≤ (1418799006549/12500000000000 : ℝ)^105 := by
    have hnat : (1886853807 : ℕ)^137*12500000000000^105 ≤ 1418799006549^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886853807 10000000000 1418799006549 12500000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083413763/2000000000 : ℝ)^137 ≤ (44939255121667/100000000000000 : ℝ)^105 := by
    have hnat : (1083413763 : ℕ)^137*100000000000000^105 ≤ 44939255121667^105*2000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083413763 2000000000 44939255121667 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651584221/5000000000 : ℝ), (-1886853807/10000000000 : ℝ), (1083413763/2000000000 : ℝ)] ![(21855176409779/50000000000000 : ℝ), (1418799006549/12500000000000 : ℝ), (44939255121667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651584221/5000000000 : ℝ)|^137 ≤ (21855176409779/50000000000000 : ℝ)^105
        have hw : |(2651584221/5000000000 : ℝ)|=(2651584221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1886853807/10000000000 : ℝ)|^137 ≤ (1418799006549/12500000000000 : ℝ)^105
        have hw : |(-1886853807/10000000000 : ℝ)|=(1886853807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083413763/2000000000 : ℝ)|^137 ≤ (44939255121667/100000000000000 : ℝ)^105
        have hw : |(1083413763/2000000000 : ℝ)|=(1083413763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1325792071/2500000000 : ℝ)*x 0 + (2708534491/5000000000 : ℝ)*x 1 + (-1886853793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325792071/2500000000 : ℝ)^137 ≤ (21855175560193/50000000000000 : ℝ)^105 := by
    have hnat : (1325792071 : ℕ)^137*50000000000000^105 ≤ 21855175560193^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325792071 2500000000 21855175560193 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708534491/5000000000 : ℝ)^137 ≤ (2808703558081/6250000000000 : ℝ)^105 := by
    have hnat : (2708534491 : ℕ)^137*6250000000000^105 ≤ 2808703558081^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708534491 5000000000 2808703558081 6250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886853793/10000000000 : ℝ)^137 ≤ (2837597985627/25000000000000 : ℝ)^105 := by
    have hnat : (1886853793 : ℕ)^137*25000000000000^105 ≤ 2837597985627^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886853793 10000000000 2837597985627 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325792071/2500000000 : ℝ), (2708534491/5000000000 : ℝ), (-1886853793/10000000000 : ℝ)] ![(21855175560193/50000000000000 : ℝ), (2808703558081/6250000000000 : ℝ), (2837597985627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325792071/2500000000 : ℝ)|^137 ≤ (21855175560193/50000000000000 : ℝ)^105
        have hw : |(1325792071/2500000000 : ℝ)|=(1325792071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708534491/5000000000 : ℝ)|^137 ≤ (2808703558081/6250000000000 : ℝ)^105
        have hw : |(2708534491/5000000000 : ℝ)|=(2708534491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1886853793/10000000000 : ℝ)|^137 ≤ (2837597985627/25000000000000 : ℝ)^105
        have hw : |(-1886853793/10000000000 : ℝ)|=(1886853793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s3_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4304993681/10000000000 : ℝ)*x 0 + (4501251369/10000000000 : ℝ)*x 1 + (1029137149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304993681/10000000000 : ℝ)^137 ≤ (33298240506807/100000000000000 : ℝ)^105 := by
    have hnat : (4304993681 : ℕ)^137*100000000000000^105 ≤ 33298240506807^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304993681 10000000000 33298240506807 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501251369/10000000000 : ℝ)^137 ≤ (35292502360671/100000000000000 : ℝ)^105 := by
    have hnat : (4501251369 : ℕ)^137*100000000000000^105 ≤ 35292502360671^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501251369 10000000000 35292502360671 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029137149/2500000000 : ℝ)^137 ≤ (31409257113737/100000000000000 : ℝ)^105 := by
    have hnat : (1029137149 : ℕ)^137*100000000000000^105 ≤ 31409257113737^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029137149 2500000000 31409257113737 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304993681/10000000000 : ℝ), (4501251369/10000000000 : ℝ), (1029137149/2500000000 : ℝ)] ![(33298240506807/100000000000000 : ℝ), (35292502360671/100000000000000 : ℝ), (31409257113737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304993681/10000000000 : ℝ)|^137 ≤ (33298240506807/100000000000000 : ℝ)^105
        have hw : |(4304993681/10000000000 : ℝ)|=(4304993681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501251369/10000000000 : ℝ)|^137 ≤ (35292502360671/100000000000000 : ℝ)^105
        have hw : |(4501251369/10000000000 : ℝ)|=(4501251369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029137149/2500000000 : ℝ)|^137 ≤ (31409257113737/100000000000000 : ℝ)^105
        have hw : |(1029137149/2500000000 : ℝ)|=(1029137149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5573/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14949/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3163/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (517/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3163/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (517/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3163/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (517/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3163/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (517/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3163/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (517/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3163/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (517/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (517/5000 : ℝ) ^ (4383/1024 : ℝ) ≤ (3025857302920561/50000000000000000000 : ℝ) := by
    have hpowers : (517/5000 : ℝ)^4383 ≤ (3025857302920561/50000000000000000000 : ℝ)^1024 := by
      have hnat : (517 : ℕ)^4383*50000000000000000000^1024 ≤ 3025857302920561^1024*5000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        517 5000 3025857302920561 50000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (517/5000 : ℝ)) (X := (3025857302920561/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3163/20000 : ℝ) ^ (4383/1024 : ℝ) ≤ (37307586572339053/100000000000000000000 : ℝ) := by
    have hpowers : (3163/20000 : ℝ)^4383 ≤ (37307586572339053/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3163 : ℕ)^4383*100000000000000000000^1024 ≤ 37307586572339053^1024*20000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163 20000 37307586572339053 100000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3163/20000 : ℝ)) (X := (37307586572339053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003025857302920561/25000000000000000000 : ℝ) ≤ (125003534490287/125000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (25003025857302920561/25000000000000000000 : ℝ)^1024 ≤ (125003534490287/125000000000000 : ℝ)^4383 := by
      have hnat : (25003025857302920561 : ℕ)^1024*125000000000000^4383 ≤ 125003534490287^4383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003025857302920561 25000000000000000000 125003534490287 125000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125003534490287/125000000000000 : ℝ)) (X := (25003025857302920561/25000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001734372047127207/4000000000000000000 : ℝ) ≤ (10001012834802731/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (4001734372047127207/4000000000000000000 : ℝ)^1024 ≤ (10001012834802731/10000000000000000 : ℝ)^4383 := by
      have hnat : (4001734372047127207 : ℕ)^1024*10000000000000000^4383 ≤ 10001012834802731^4383*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001734372047127207 4000000000000000000 10001012834802731 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001012834802731/10000000000000000 : ℝ)) (X := (4001734372047127207/4000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037307586572339053/50000000000000000000 : ℝ) ≤ (5000871455191251/5000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50037307586572339053/50000000000000000000 : ℝ)^1024 ≤ (5000871455191251/5000000000000000 : ℝ)^4383 := by
      have hnat : (50037307586572339053 : ℕ)^1024*5000000000000000^4383 ≤ 5000871455191251^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037307586572339053 50000000000000000000 5000871455191251 5000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000871455191251/5000000000000000 : ℝ)) (X := (50037307586572339053/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3025857302920561/50000000000000000000 : ℝ) ≤ ((1368411253593901043/1368750000000000000 : ℝ)+2*(730075579771/547500000000000 : ℝ)*(517/5000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (1368411253593901043/1368750000000000000 : ℝ)+2*(730075579771/547500000000000 : ℝ)*(517/5000 : ℝ)=(125003534490287/125000000000000 : ℝ) by norm_num, show 1+2*(3025857302920561/50000000000000000000 : ℝ)=(25003025857302920561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37307586572339053/100000000000000000000 : ℝ)+(3025857302920561/50000000000000000000 : ℝ) ≤ ((1368411253593901043/1368750000000000000 : ℝ)+(730075579771/547500000000000 : ℝ)*((3163/20000 : ℝ)+(517/5000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (1368411253593901043/1368750000000000000 : ℝ)+(730075579771/547500000000000 : ℝ)*((3163/20000 : ℝ)+(517/5000 : ℝ))=(10001012834802731/10000000000000000 : ℝ) by norm_num, show 1+(37307586572339053/100000000000000000000 : ℝ)+(3025857302920561/50000000000000000000 : ℝ)=(4001734372047127207/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37307586572339053/100000000000000000000 : ℝ) ≤ ((1368411253593901043/1368750000000000000 : ℝ)+2*(730075579771/547500000000000 : ℝ)*(3163/20000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (1368411253593901043/1368750000000000000 : ℝ)+2*(730075579771/547500000000000 : ℝ)*(3163/20000 : ℝ)=(5000871455191251/5000000000000000 : ℝ) by norm_num, show 1+2*(37307586572339053/100000000000000000000 : ℝ)=(50037307586572339053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1368411253593901043/1368750000000000000 : ℝ)*(X 1 0+X 2 0)+(730075579771/547500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (517/5000 : ℝ)) (hi := (3163/20000 : ℝ)) (c := (1368411253593901043/1368750000000000000 : ℝ)) (alpha := (730075579771/547500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1368411253593901043/1368750000000000000 : ℝ)*(X 0 1+X 2 1)+(730075579771/547500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (517/5000 : ℝ)) (hi := (3163/20000 : ℝ)) (c := (1368411253593901043/1368750000000000000 : ℝ)) (alpha := (730075579771/547500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1368411253593901043/1368750000000000000 : ℝ)*(X 0 2+X 1 2)+(730075579771/547500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (517/5000 : ℝ)) (hi := (3163/20000 : ℝ)) (c := (1368411253593901043/1368750000000000000 : ℝ)) (alpha := (730075579771/547500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987053459/5000000000 : ℝ)*X 0 0+(338611969/625000000 : ℝ)*X 0 1+(1309548789/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668729373/1250000000 : ℝ)*X 1 0+(-2065727477/10000000000 : ℝ)*X 1 1+(2619097563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069967/2000000 : ℝ)*X 2 0+(5238195123/10000000000 : ℝ)*X 2 1+(-103286373/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152480139/5000000000 : ℝ)*X 0 0+(4114987827/10000000000 : ℝ)*X 0 1+(4502802999/10000000000 : ℝ)*X 0 2+(2152480139/5000000000 : ℝ)*X 1 0+(4114987827/10000000000 : ℝ)*X 1 1+(4502802999/10000000000 : ℝ)*X 1 2+(2152480139/5000000000 : ℝ)*X 2 0+(4114987827/10000000000 : ℝ)*X 2 1+(4502802999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-987061117/5000000000 : ℝ)*X 0 0+(654864237/1250000000 : ℝ)*X 0 1+(5417068821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651584221/5000000000 : ℝ)*X 1 0+(-1886853807/10000000000 : ℝ)*X 1 1+(1083413763/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325792071/2500000000 : ℝ)*X 2 0+(2708534491/5000000000 : ℝ)*X 2 1+(-1886853793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4304993681/10000000000 : ℝ)*X 0 0+(4501251369/10000000000 : ℝ)*X 0 1+(1029137149/2500000000 : ℝ)*X 0 2+(4304993681/10000000000 : ℝ)*X 1 0+(4501251369/10000000000 : ℝ)*X 1 1+(1029137149/2500000000 : ℝ)*X 1 2+(4304993681/10000000000 : ℝ)*X 2 0+(4501251369/10000000000 : ℝ)*X 2 1+(1029137149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22304517394597769663827809/2851562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1471802751/100000000000000 : ℝ)*(base19) + (144640581/10000000000000 : ℝ)*(base23) + (209641963/100000000000000 : ℝ)*(upper3) + (11247947/50000000000000 : ℝ)*(upper4) + (101265247/50000000000000 : ℝ)*(upper5) + (1018333245888901/25000000000000 : ℝ)*(major0) + (1018333245888901/25000000000000 : ℝ)*(major1) + (1018333245888901/25000000000000 : ℝ)*(major2) + (5568067895145573/100000000000000 : ℝ)*(sp0) + (1113618590061139/20000000000000 : ℝ)*(sp1) + (5568092975702637/100000000000000 : ℝ)*(sp2) + (1289279700893759/50000000000000 : ℝ)*(sp3) + (26526962873/100000000000000 : ℝ)*(sp4) + (1188248663/10000000000000 : ℝ)*(sp7) + (644642821068537/25000000000000 : ℝ)*(f.failure) + (5568094422108447/100000000000000 : ℝ)*(f.sum) + (91247566933033/13687500000000000000000000000 : ℝ)*base66 + (49894031761182919/11406250000000000000000000000000 : ℝ)*base68 + (25309345287901669/11406250000000000000000000000000 : ℝ)*base70 + (23574042110245419/11406250000000000000000000000000 : ℝ)*base72 + (121343643498191/27375000000000000000000000000 : ℝ)*base74 + (200503431621942081/11406250000000000000000000000000 : ℝ)*base75 + (17380541989754581/11406250000000000000000000000000 : ℝ)*base77 + (145173225139776669/11406250000000000000000000000000 : ℝ)*base80 + (10985753287783/13687500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (15006737/2500000000000000000000 : ℝ)*base89 + (15006737/2500000000000000000000 : ℝ)*base91 + (15006737/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61505667401410230891856161/11406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76330907/20000000000000 : ℝ)*(base19) + (79049279/25000000000000 : ℝ)*(base23) + (27230143/50000000000000 : ℝ)*(upper3) + (23357849/50000000000000 : ℝ)*(lower4) + (5300901/10000000000000 : ℝ)*(upper5) + (2053124689200223/50000000000000 : ℝ)*(major0) + (2053124689200223/50000000000000 : ℝ)*(major1) + (2053124689200223/50000000000000 : ℝ)*(major2) + (1309097021/20000000000000 : ℝ)*(sp1) + (8100733447/100000000000000 : ℝ)*(sp2) + (350818124408607/6250000000000 : ℝ)*(sp4) + (701635382924759/12500000000000 : ℝ)*(sp5) + (5613081573607149/100000000000000 : ℝ)*(sp6) + (2599408586520587/100000000000000 : ℝ)*(sp7) + (2599408586520587/100000000000000 : ℝ)*(f.failure) + (350818124408607/6250000000000 : ℝ)*(f.sum) + (103460286422741/27375000000000000000000000000 : ℝ)*base65 + (68068889650850863/22812500000000000000000000000000 : ℝ)*base67 + (38947733095538363/22812500000000000000000000000000 : ℝ)*base69 + (97152811985850863/22812500000000000000000000000000 : ℝ)*base71 + (2026626820619/427734375000000000000000000 : ℝ)*base73 + (38136739133836637/22812500000000000000000000000000 : ℝ)*base76 + (56324136187100863/22812500000000000000000000000000 : ℝ)*base77 + (13848182327586637/22812500000000000000000000000000 : ℝ)*base80 + (114073493549741/27375000000000000000000000000 : ℝ)*base81 + (13911213/10000000000000000000000 : ℝ)*base90 + (13911213/10000000000000000000000 : ℝ)*base92 + (13911213/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1424_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14949/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1424_s4_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1975033369/10000000000 : ℝ)*x 0 + (676237699/1250000000 : ℝ)*x 1 + (20490137/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1975033369/10000000000 : ℝ)^137 ≤ (12047373129349/100000000000000 : ℝ)^105 := by
    have hnat : (1975033369 : ℕ)^137*100000000000000^105 ≤ 12047373129349^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975033369 10000000000 12047373129349 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676237699/1250000000 : ℝ)^137 ≤ (8972338370433/20000000000000 : ℝ)^105 := by
    have hnat : (676237699 : ℕ)^137*20000000000000^105 ≤ 8972338370433^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676237699 1250000000 8972338370433 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20490137/39062500 : ℝ)^137 ≤ (21545467505699/50000000000000 : ℝ)^105 := by
    have hnat : (20490137 : ℕ)^137*50000000000000^105 ≤ 21545467505699^105*39062500^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20490137 39062500 21545467505699 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1975033369/10000000000 : ℝ), (676237699/1250000000 : ℝ), (20490137/39062500 : ℝ)] ![(12047373129349/100000000000000 : ℝ), (8972338370433/20000000000000 : ℝ), (21545467505699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1975033369/10000000000 : ℝ)|^137 ≤ (12047373129349/100000000000000 : ℝ)^105
        have hw : |(-1975033369/10000000000 : ℝ)|=(1975033369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676237699/1250000000 : ℝ)|^137 ≤ (8972338370433/20000000000000 : ℝ)^105
        have hw : |(676237699/1250000000 : ℝ)|=(676237699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20490137/39062500 : ℝ)|^137 ≤ (21545467505699/50000000000000 : ℝ)^105
        have hw : |(20490137/39062500 : ℝ)|=(20490137/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5347800009/10000000000 : ℝ)*x 0 + (-1029387209/5000000000 : ℝ)*x 1 + (1311368777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347800009/10000000000 : ℝ)^137 ≤ (22095473115529/50000000000000 : ℝ)^105 := by
    have hnat : (5347800009 : ℕ)^137*50000000000000^105 ≤ 22095473115529^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347800009 10000000000 22095473115529 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029387209/5000000000 : ℝ)^137 ≤ (6359059179887/50000000000000 : ℝ)^105 := by
    have hnat : (1029387209 : ℕ)^137*50000000000000^105 ≤ 6359059179887^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029387209 5000000000 6359059179887 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311368777/2500000000 : ℝ)^137 ≤ (43090935397263/100000000000000 : ℝ)^105 := by
    have hnat : (1311368777 : ℕ)^137*100000000000000^105 ≤ 43090935397263^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311368777 2500000000 43090935397263 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347800009/10000000000 : ℝ), (-1029387209/5000000000 : ℝ), (1311368777/2500000000 : ℝ)] ![(22095473115529/50000000000000 : ℝ), (6359059179887/50000000000000 : ℝ), (43090935397263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347800009/10000000000 : ℝ)|^137 ≤ (22095473115529/50000000000000 : ℝ)^105
        have hw : |(5347800009/10000000000 : ℝ)|=(5347800009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1029387209/5000000000 : ℝ)|^137 ≤ (6359059179887/50000000000000 : ℝ)^105
        have hw : |(-1029387209/5000000000 : ℝ)|=(1029387209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311368777/2500000000 : ℝ)|^137 ≤ (43090935397263/100000000000000 : ℝ)^105
        have hw : |(1311368777/2500000000 : ℝ)|=(1311368777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5347800007/10000000000 : ℝ)*x 0 + (5245475117/10000000000 : ℝ)*x 1 + (-257346801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347800007/10000000000 : ℝ)^137 ≤ (8838189241899/20000000000000 : ℝ)^105 := by
    have hnat : (5347800007 : ℕ)^137*20000000000000^105 ≤ 8838189241899^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347800007 10000000000 8838189241899 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245475117/10000000000 : ℝ)^137 ≤ (43090935493729/100000000000000 : ℝ)^105 := by
    have hnat : (5245475117 : ℕ)^137*100000000000000^105 ≤ 43090935493729^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245475117 10000000000 43090935493729 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257346801/1250000000 : ℝ)^137 ≤ (3179529569793/25000000000000 : ℝ)^105 := by
    have hnat : (257346801 : ℕ)^137*25000000000000^105 ≤ 3179529569793^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257346801 1250000000 3179529569793 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347800007/10000000000 : ℝ), (5245475117/10000000000 : ℝ), (-257346801/1250000000 : ℝ)] ![(8838189241899/20000000000000 : ℝ), (43090935493729/100000000000000 : ℝ), (3179529569793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347800007/10000000000 : ℝ)|^137 ≤ (8838189241899/20000000000000 : ℝ)^105
        have hw : |(5347800007/10000000000 : ℝ)|=(5347800007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245475117/10000000000 : ℝ)|^137 ≤ (43090935493729/100000000000000 : ℝ)^105
        have hw : |(5245475117/10000000000 : ℝ)|=(5245475117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257346801/1250000000 : ℝ)|^137 ≤ (3179529569793/25000000000000 : ℝ)^105
        have hw : |(-257346801/1250000000 : ℝ)|=(257346801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4305527813/10000000000 : ℝ)*x 0 + (2065648969/5000000000 : ℝ)*x 1 + (1121588979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305527813/10000000000 : ℝ)^137 ≤ (16651815551769/50000000000000 : ℝ)^105 := by
    have hnat : (4305527813 : ℕ)^137*50000000000000^105 ≤ 16651815551769^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305527813 10000000000 16651815551769 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065648969/5000000000 : ℝ)^137 ≤ (6311234358059/20000000000000 : ℝ)^105 := by
    have hnat : (2065648969 : ℕ)^137*20000000000000^105 ≤ 6311234358059^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065648969 5000000000 6311234358059 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121588979/2500000000 : ℝ)^137 ≤ (35140197083809/100000000000000 : ℝ)^105 := by
    have hnat : (1121588979 : ℕ)^137*100000000000000^105 ≤ 35140197083809^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121588979 2500000000 35140197083809 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305527813/10000000000 : ℝ), (2065648969/5000000000 : ℝ), (1121588979/2500000000 : ℝ)] ![(16651815551769/50000000000000 : ℝ), (6311234358059/20000000000000 : ℝ), (35140197083809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305527813/10000000000 : ℝ)|^137 ≤ (16651815551769/50000000000000 : ℝ)^105
        have hw : |(4305527813/10000000000 : ℝ)|=(4305527813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065648969/5000000000 : ℝ)|^137 ≤ (6311234358059/20000000000000 : ℝ)^105
        have hw : |(2065648969/5000000000 : ℝ)|=(2065648969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121588979/2500000000 : ℝ)|^137 ≤ (35140197083809/100000000000000 : ℝ)^105
        have hw : |(1121588979/2500000000 : ℝ)|=(1121588979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-123440333/625000000 : ℝ)*x 0 + (5246077877/10000000000 : ℝ)*x 1 + (5409295613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123440333/625000000 : ℝ)^137 ≤ (3011867077269/25000000000000 : ℝ)^105 := by
    have hnat : (123440333 : ℕ)^137*25000000000000^105 ≤ 3011867077269^105*625000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123440333 625000000 3011867077269 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246077877/10000000000 : ℝ)^137 ≤ (21548698132663/50000000000000 : ℝ)^105 := by
    have hnat : (5246077877 : ℕ)^137*50000000000000^105 ≤ 21548698132663^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246077877 10000000000 21548698132663 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409295613/10000000000 : ℝ)^137 ≤ (11213783854473/25000000000000 : ℝ)^105 := by
    have hnat : (5409295613 : ℕ)^137*25000000000000^105 ≤ 11213783854473^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409295613 10000000000 11213783854473 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123440333/625000000 : ℝ), (5246077877/10000000000 : ℝ), (5409295613/10000000000 : ℝ)] ![(3011867077269/25000000000000 : ℝ), (21548698132663/50000000000000 : ℝ), (11213783854473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123440333/625000000 : ℝ)|^137 ≤ (3011867077269/25000000000000 : ℝ)^105
        have hw : |(-123440333/625000000 : ℝ)|=(123440333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246077877/10000000000 : ℝ)|^137 ≤ (21548698132663/50000000000000 : ℝ)^105
        have hw : |(5246077877/10000000000 : ℝ)|=(5246077877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409295613/10000000000 : ℝ)|^137 ≤ (11213783854473/25000000000000 : ℝ)^105
        have hw : |(5409295613/10000000000 : ℝ)|=(5409295613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1326268679/2500000000 : ℝ)*x 0 + (-1894953883/10000000000 : ℝ)*x 1 + (270464783/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326268679/2500000000 : ℝ)^137 ≤ (21865427245487/50000000000000 : ℝ)^105 := by
    have hnat : (1326268679 : ℕ)^137*50000000000000^105 ≤ 21865427245487^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326268679 2500000000 21865427245487 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1894953883/10000000000 : ℝ)^137 ≤ (11414009566343/100000000000000 : ℝ)^105 := by
    have hnat : (1894953883 : ℕ)^137*100000000000000^105 ≤ 11414009566343^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1894953883 10000000000 11414009566343 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270464783/500000000 : ℝ)^137 ≤ (44855135926403/100000000000000 : ℝ)^105 := by
    have hnat : (270464783 : ℕ)^137*100000000000000^105 ≤ 44855135926403^105*500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270464783 500000000 44855135926403 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326268679/2500000000 : ℝ), (-1894953883/10000000000 : ℝ), (270464783/500000000 : ℝ)] ![(21865427245487/50000000000000 : ℝ), (11414009566343/100000000000000 : ℝ), (44855135926403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326268679/2500000000 : ℝ)|^137 ≤ (21865427245487/50000000000000 : ℝ)^105
        have hw : |(1326268679/2500000000 : ℝ)|=(1326268679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1894953883/10000000000 : ℝ)|^137 ≤ (11414009566343/100000000000000 : ℝ)^105
        have hw : |(-1894953883/10000000000 : ℝ)|=(1894953883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270464783/500000000 : ℝ)|^137 ≤ (44855135926403/100000000000000 : ℝ)^105
        have hw : |(270464783/500000000 : ℝ)|=(270464783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305074731/10000000000 : ℝ)*x 0 + (2704647833/5000000000 : ℝ)*x 1 + (-947476927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305074731/10000000000 : ℝ)^137 ≤ (8746170930461/20000000000000 : ℝ)^105 := by
    have hnat : (5305074731 : ℕ)^137*20000000000000^105 ≤ 8746170930461^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305074731 10000000000 8746170930461 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704647833/5000000000 : ℝ)^137 ≤ (44855135991319/100000000000000 : ℝ)^105 := by
    have hnat : (2704647833 : ℕ)^137*100000000000000^105 ≤ 44855135991319^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704647833 5000000000 44855135991319 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947476927/5000000000 : ℝ)^137 ≤ (1141400933843/10000000000000 : ℝ)^105 := by
    have hnat : (947476927 : ℕ)^137*10000000000000^105 ≤ 1141400933843^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947476927 5000000000 1141400933843 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305074731/10000000000 : ℝ), (2704647833/5000000000 : ℝ), (-947476927/5000000000 : ℝ)] ![(8746170930461/20000000000000 : ℝ), (44855135991319/100000000000000 : ℝ), (1141400933843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305074731/10000000000 : ℝ)|^137 ≤ (8746170930461/20000000000000 : ℝ)^105
        have hw : |(5305074731/10000000000 : ℝ)|=(5305074731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704647833/5000000000 : ℝ)|^137 ≤ (44855135991319/100000000000000 : ℝ)^105
        have hw : |(2704647833/5000000000 : ℝ)|=(2704647833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947476927/5000000000 : ℝ)|^137 ≤ (1141400933843/10000000000000 : ℝ)^105
        have hw : |(-947476927/5000000000 : ℝ)|=(947476927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s4_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (430555363/1000000000 : ℝ)*x 0 + (2242527167/5000000000 : ℝ)*x 1 + (2066303187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430555363/1000000000 : ℝ)^137 ≤ (8325972915117/25000000000000 : ℝ)^105 := by
    have hnat : (430555363 : ℕ)^137*25000000000000^105 ≤ 8325972915117^105*1000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430555363 1000000000 8325972915117 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242527167/5000000000 : ℝ)^137 ≤ (35126895784409/100000000000000 : ℝ)^105 := by
    have hnat : (2242527167 : ℕ)^137*100000000000000^105 ≤ 35126895784409^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242527167 5000000000 35126895784409 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066303187/5000000000 : ℝ)^137 ≤ (6313842507677/20000000000000 : ℝ)^105 := by
    have hnat : (2066303187 : ℕ)^137*20000000000000^105 ≤ 6313842507677^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066303187 5000000000 6313842507677 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430555363/1000000000 : ℝ), (2242527167/5000000000 : ℝ), (2066303187/5000000000 : ℝ)] ![(8325972915117/25000000000000 : ℝ), (35126895784409/100000000000000 : ℝ), (6313842507677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430555363/1000000000 : ℝ)|^137 ≤ (8325972915117/25000000000000 : ℝ)^105
        have hw : |(430555363/1000000000 : ℝ)|=(430555363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242527167/5000000000 : ℝ)|^137 ≤ (35126895784409/100000000000000 : ℝ)^105
        have hw : |(2242527167/5000000000 : ℝ)|=(2242527167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066303187/5000000000 : ℝ)|^137 ≤ (6313842507677/20000000000000 : ℝ)^105
        have hw : |(2066303187/5000000000 : ℝ)|=(2066303187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14949/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5651/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (462/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14949/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14949/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5573/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14949/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14949/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5573/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14949/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14949/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5573/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5573/50000 : ℝ) ^ (4383/1024 : ℝ) ≤ (4172332748820007/50000000000000000000 : ℝ) := by
    have hpowers : (5573/50000 : ℝ)^4383 ≤ (4172332748820007/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5573 : ℕ)^4383*50000000000000000000^1024 ≤ 4172332748820007^1024*50000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5573 50000 4172332748820007 50000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5573/50000 : ℝ)) (X := (4172332748820007/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14949/100000 : ℝ) ^ (4383/1024 : ℝ) ≤ (29316645485637319/100000000000000000000 : ℝ) := by
    have hpowers : (14949/100000 : ℝ)^4383 ≤ (29316645485637319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14949 : ℕ)^4383*100000000000000000000^1024 ≤ 29316645485637319^1024*100000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14949 100000 29316645485637319 100000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14949/100000 : ℝ)) (X := (29316645485637319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004172332748820007/25000000000000000000 : ℝ) ≤ (10000389887796753/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (25004172332748820007/25000000000000000000 : ℝ)^1024 ≤ (10000389887796753/10000000000000000 : ℝ)^4383 := by
      have hnat : (25004172332748820007 : ℕ)^1024*10000000000000000^4383 ≤ 10000389887796753^4383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004172332748820007 25000000000000000000 10000389887796753 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000389887796753/10000000000000000 : ℝ)) (X := (25004172332748820007/25000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037661310983277333/100000000000000000000 : ℝ) ≤ (250021993850241/250000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (100037661310983277333/100000000000000000000 : ℝ)^1024 ≤ (250021993850241/250000000000000 : ℝ)^4383 := by
      have hnat : (100037661310983277333 : ℕ)^1024*250000000000000^4383 ≤ 250021993850241^4383*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037661310983277333 100000000000000000000 250021993850241 250000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250021993850241/250000000000000 : ℝ)) (X := (100037661310983277333/100000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029316645485637319/50000000000000000000 : ℝ) ≤ (10001369620222527/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50029316645485637319/50000000000000000000 : ℝ)^1024 ≤ (10001369620222527/10000000000000000 : ℝ)^4383 := by
      have hnat : (50029316645485637319 : ℕ)^1024*10000000000000000^4383 ≤ 10001369620222527^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029316645485637319 50000000000000000000 10001369620222527 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001369620222527/10000000000000000 : ℝ)) (X := (50029316645485637319/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4172332748820007/50000000000000000000 : ℝ) ≤ ((7604112529134674931/7606000000000000000 : ℝ)+2*(489866212887/380300000000000 : ℝ)*(5573/50000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (7604112529134674931/7606000000000000000 : ℝ)+2*(489866212887/380300000000000 : ℝ)*(5573/50000 : ℝ)=(10000389887796753/10000000000000000 : ℝ) by norm_num, show 1+2*(4172332748820007/50000000000000000000 : ℝ)=(25004172332748820007/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29316645485637319/100000000000000000000 : ℝ)+(4172332748820007/50000000000000000000 : ℝ) ≤ ((7604112529134674931/7606000000000000000 : ℝ)+(489866212887/380300000000000 : ℝ)*((14949/100000 : ℝ)+(5573/50000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (7604112529134674931/7606000000000000000 : ℝ)+(489866212887/380300000000000 : ℝ)*((14949/100000 : ℝ)+(5573/50000 : ℝ))=(250021993850241/250000000000000 : ℝ) by norm_num, show 1+(29316645485637319/100000000000000000000 : ℝ)+(4172332748820007/50000000000000000000 : ℝ)=(100037661310983277333/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29316645485637319/100000000000000000000 : ℝ) ≤ ((7604112529134674931/7606000000000000000 : ℝ)+2*(489866212887/380300000000000 : ℝ)*(14949/100000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (7604112529134674931/7606000000000000000 : ℝ)+2*(489866212887/380300000000000 : ℝ)*(14949/100000 : ℝ)=(10001369620222527/10000000000000000 : ℝ) by norm_num, show 1+2*(29316645485637319/100000000000000000000 : ℝ)=(50029316645485637319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7604112529134674931/7606000000000000000 : ℝ)*(X 1 0+X 2 0)+(489866212887/380300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (14949/100000 : ℝ)) (c := (7604112529134674931/7606000000000000000 : ℝ)) (alpha := (489866212887/380300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7604112529134674931/7606000000000000000 : ℝ)*(X 0 1+X 2 1)+(489866212887/380300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (14949/100000 : ℝ)) (c := (7604112529134674931/7606000000000000000 : ℝ)) (alpha := (489866212887/380300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7604112529134674931/7606000000000000000 : ℝ)*(X 0 2+X 1 2)+(489866212887/380300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5573/50000 : ℝ)) (hi := (14949/100000 : ℝ)) (c := (7604112529134674931/7606000000000000000 : ℝ)) (alpha := (489866212887/380300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1975033369/10000000000 : ℝ)*X 0 0+(676237699/1250000000 : ℝ)*X 0 1+(20490137/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347800009/10000000000 : ℝ)*X 1 0+(-1029387209/5000000000 : ℝ)*X 1 1+(1311368777/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347800007/10000000000 : ℝ)*X 2 0+(5245475117/10000000000 : ℝ)*X 2 1+(-257346801/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4305527813/10000000000 : ℝ)*X 0 0+(2065648969/5000000000 : ℝ)*X 0 1+(1121588979/2500000000 : ℝ)*X 0 2+(4305527813/10000000000 : ℝ)*X 1 0+(2065648969/5000000000 : ℝ)*X 1 1+(1121588979/2500000000 : ℝ)*X 1 2+(4305527813/10000000000 : ℝ)*X 2 0+(2065648969/5000000000 : ℝ)*X 2 1+(1121588979/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-123440333/625000000 : ℝ)*X 0 0+(5246077877/10000000000 : ℝ)*X 0 1+(5409295613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326268679/2500000000 : ℝ)*X 1 0+(-1894953883/10000000000 : ℝ)*X 1 1+(270464783/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305074731/10000000000 : ℝ)*X 2 0+(2704647833/5000000000 : ℝ)*X 2 1+(-947476927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((430555363/1000000000 : ℝ)*X 0 0+(2242527167/5000000000 : ℝ)*X 0 1+(2066303187/5000000000 : ℝ)*X 0 2+(430555363/1000000000 : ℝ)*X 1 0+(2242527167/5000000000 : ℝ)*X 1 1+(2066303187/5000000000 : ℝ)*X 1 2+(430555363/1000000000 : ℝ)*X 2 0+(2242527167/5000000000 : ℝ)*X 2 1+(2066303187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31130969856663449390841387/11884375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (421373537/100000000000000 : ℝ)*(base19) + (193870719/50000000000000 : ℝ)*(base23) + (16769421/100000000000000 : ℝ)*(lower2) + (27793151/50000000000000 : ℝ)*(upper3) + (1388381/3125000000000 : ℝ)*(upper5) + (69517303752683/1562500000000 : ℝ)*(major0) + (69517303752683/1562500000000 : ℝ)*(major1) + (69517303752683/1562500000000 : ℝ)*(major2) + (243270165127031/4000000000000 : ℝ)*(sp0) + (6081763879589253/100000000000000 : ℝ)*(sp1) + (760220489152669/12500000000000 : ℝ)*(sp2) + (2816445799513921/100000000000000 : ℝ)*(sp3) + (2034557403/20000000000000 : ℝ)*(sp4) + (586568807/12500000000000 : ℝ)*(sp7) + (352056311508047/12500000000000 : ℝ)*(f.failure) + (608176430096279/10000000000000 : ℝ)*(f.sum) + (60109958035913/9507500000000000000000000000 : ℝ)*base66 + (60556490018581499/5942187500000000000000000000000 : ℝ)*base67 + (8413576487805047/742773437500000000000000000000 : ℝ)*base70 + (128489954190541123/11884375000000000000000000000000 : ℝ)*base71 + (538186172647/2376875000000000000000000000 : ℝ)*base74 + (52094124289840127/11884375000000000000000000000000 : ℝ)*base76 + (55281507018456499/5942187500000000000000000000000 : ℝ)*base77 + (59594734218766123/11884375000000000000000000000000 : ℝ)*base79 + (24114053191729/4753750000000000000000000000 : ℝ)*base82 + (15167753/1250000000000000000000 : ℝ)*base90 + (15167753/1250000000000000000000 : ℝ)*base92 + (15167753/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26357718671695166235539247/5942187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (331899937/50000000000000 : ℝ)*(base19) + (758754123/100000000000000 : ℝ)*(base23) + (21041273/20000000000000 : ℝ)*(upper3) + (2675677/10000000000000 : ℝ)*(lower4) + (34620511/50000000000000 : ℝ)*(upper5) + (70031893379279/1562500000000 : ℝ)*(major0) + (70031893379279/1562500000000 : ℝ)*(major1) + (70031893379279/1562500000000 : ℝ)*(major2) + (13937226433/100000000000000 : ℝ)*(sp1) + (8656960171/50000000000000 : ℝ)*(sp2) + (6126783432719589/100000000000000 : ℝ)*(sp4) + (3063384415846641/50000000000000 : ℝ)*(sp5) + (6126765360045123/100000000000000 : ℝ)*(sp6) + (354662346496461/12500000000000 : ℝ)*(sp7) + (354662346496461/12500000000000 : ℝ)*(f.failure) + (6126783432719589/100000000000000 : ℝ)*(f.sum) + (408681381611/594218750000000000000000000 : ℝ)*base65 + (38365444430997313/5942187500000000000000000000000 : ℝ)*base68 + (20350653048265187/5942187500000000000000000000000 : ℝ)*base69 + (46771826805859813/5942187500000000000000000000000 : ℝ)*base72 + (7226011440951/2376875000000000000000000000 : ℝ)*base74 + (32958321438097751/11884375000000000000000000000000 : ℝ)*base76 + (213332055796457/371386718750000000000000000000 : ℝ)*base77 + (92085909934922751/11884375000000000000000000000000 : ℝ)*base80 + (28061215385131/9507500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4378939/1250000000000000000000 : ℝ)*base90 + (4378939/1250000000000000000000 : ℝ)*base92 + (4378939/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1424_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14949/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (462/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1424_s5_0 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1975172183/10000000000 : ℝ)*x 0 + (2704331821/5000000000 : ℝ)*x 1 + (5246621563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1975172183/10000000000 : ℝ)^137 ≤ (3012119484529/25000000000000 : ℝ)^105 := by
    have hnat : (1975172183 : ℕ)^137*25000000000000^105 ≤ 3012119484529^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975172183 10000000000 3012119484529 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704331821/5000000000 : ℝ)^137 ≤ (8969659599943/20000000000000 : ℝ)^105 := by
    have hnat : (2704331821 : ℕ)^137*20000000000000^105 ≤ 8969659599943^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704331821 5000000000 8969659599943 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246621563/10000000000 : ℝ)^137 ≤ (43103224037641/100000000000000 : ℝ)^105 := by
    have hnat : (5246621563 : ℕ)^137*100000000000000^105 ≤ 43103224037641^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246621563 10000000000 43103224037641 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1975172183/10000000000 : ℝ), (2704331821/5000000000 : ℝ), (5246621563/10000000000 : ℝ)] ![(3012119484529/25000000000000 : ℝ), (8969659599943/20000000000000 : ℝ), (43103224037641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1975172183/10000000000 : ℝ)|^137 ≤ (3012119484529/25000000000000 : ℝ)^105
        have hw : |(-1975172183/10000000000 : ℝ)|=(1975172183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704331821/5000000000 : ℝ)|^137 ≤ (8969659599943/20000000000000 : ℝ)^105
        have hw : |(2704331821/5000000000 : ℝ)|=(2704331821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246621563/10000000000 : ℝ)|^137 ≤ (43103224037641/100000000000000 : ℝ)^105
        have hw : |(5246621563/10000000000 : ℝ)|=(5246621563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_1 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5347480461/10000000000 : ℝ)*x 0 + (-1028838521/5000000000 : ℝ)*x 1 + (1311655413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347480461/10000000000 : ℝ)^137 ≤ (44187500974559/100000000000000 : ℝ)^105 := by
    have hnat : (5347480461 : ℕ)^137*100000000000000^105 ≤ 44187500974559^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347480461 10000000000 44187500974559 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028838521/5000000000 : ℝ)^137 ≤ (1270927401743/10000000000000 : ℝ)^105 := by
    have hnat : (1028838521 : ℕ)^137*10000000000000^105 ≤ 1270927401743^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028838521 5000000000 1270927401743 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311655413/2500000000 : ℝ)^137 ≤ (1346975780989/3125000000000 : ℝ)^105 := by
    have hnat : (1311655413 : ℕ)^137*3125000000000^105 ≤ 1346975780989^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311655413 2500000000 1346975780989 3125000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347480461/10000000000 : ℝ), (-1028838521/5000000000 : ℝ), (1311655413/2500000000 : ℝ)] ![(44187500974559/100000000000000 : ℝ), (1270927401743/10000000000000 : ℝ), (1346975780989/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347480461/10000000000 : ℝ)|^137 ≤ (44187500974559/100000000000000 : ℝ)^105
        have hw : |(5347480461/10000000000 : ℝ)|=(5347480461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028838521/5000000000 : ℝ)|^137 ≤ (1270927401743/10000000000000 : ℝ)^105
        have hw : |(-1028838521/5000000000 : ℝ)|=(1028838521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311655413/2500000000 : ℝ)|^137 ≤ (1346975780989/3125000000000 : ℝ)^105
        have hw : |(1311655413/2500000000 : ℝ)|=(1311655413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_2 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8555969/16000000 : ℝ)*x 0 + (5246621549/10000000000 : ℝ)*x 1 + (-12860481/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8555969/16000000 : ℝ)^137 ≤ (22093751371367/50000000000000 : ℝ)^105 := by
    have hnat : (8555969 : ℕ)^137*50000000000000^105 ≤ 22093751371367^105*16000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8555969 16000000 22093751371367 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246621549/10000000000 : ℝ)^137 ≤ (43103223887573/100000000000000 : ℝ)^105 := by
    have hnat : (5246621549 : ℕ)^137*100000000000000^105 ≤ 43103223887573^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246621549 10000000000 43103223887573 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12860481/62500000 : ℝ)^137 ≤ (6354636678301/50000000000000 : ℝ)^105 := by
    have hnat : (12860481 : ℕ)^137*50000000000000^105 ≤ 6354636678301^105*62500000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12860481 62500000 6354636678301 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8555969/16000000 : ℝ), (5246621549/10000000000 : ℝ), (-12860481/62500000 : ℝ)] ![(22093751371367/50000000000000 : ℝ), (43103223887573/100000000000000 : ℝ), (6354636678301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8555969/16000000 : ℝ)|^137 ≤ (22093751371367/50000000000000 : ℝ)^105
        have hw : |(8555969/16000000 : ℝ)|=(8555969/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246621549/10000000000 : ℝ)|^137 ≤ (43103223887573/100000000000000 : ℝ)^105
        have hw : |(5246621549/10000000000 : ℝ)|=(5246621549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12860481/62500000 : ℝ)|^137 ≤ (6354636678301/50000000000000 : ℝ)^105
        have hw : |(-12860481/62500000 : ℝ)|=(12860481/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_3 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2152806341/5000000000 : ℝ)*x 0 + (516732767/1250000000 : ℝ)*x 1 + (70058923/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152806341/5000000000 : ℝ)^137 ≤ (16652243820977/50000000000000 : ℝ)^105 := by
    have hnat : (2152806341 : ℕ)^137*50000000000000^105 ≤ 16652243820977^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152806341 5000000000 16652243820977 50000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516732767/1250000000 : ℝ)^137 ≤ (31581729485587/100000000000000 : ℝ)^105 := by
    have hnat : (516732767 : ℕ)^137*100000000000000^105 ≤ 31581729485587^105*1250000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516732767 1250000000 31581729485587 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70058923/156250000 : ℝ)^137 ≤ (1755689142741/5000000000000 : ℝ)^105 := by
    have hnat : (70058923 : ℕ)^137*5000000000000^105 ≤ 1755689142741^105*156250000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70058923 156250000 1755689142741 5000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152806341/5000000000 : ℝ), (516732767/1250000000 : ℝ), (70058923/156250000 : ℝ)] ![(16652243820977/50000000000000 : ℝ), (31581729485587/100000000000000 : ℝ), (1755689142741/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152806341/5000000000 : ℝ)|^137 ≤ (16652243820977/50000000000000 : ℝ)^105
        have hw : |(2152806341/5000000000 : ℝ)|=(2152806341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516732767/1250000000 : ℝ)|^137 ≤ (31581729485587/100000000000000 : ℝ)^105
        have hw : |(516732767/1250000000 : ℝ)|=(516732767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70058923/156250000 : ℝ)|^137 ≤ (1755689142741/5000000000000 : ℝ)^105
        have hw : |(70058923/156250000 : ℝ)|=(70058923/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_4 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-987591849/5000000000 : ℝ)*x 0 + (2623603499/5000000000 : ℝ)*x 1 + (5408075119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987591849/5000000000 : ℝ)^137 ≤ (75303559913/625000000000 : ℝ)^105 := by
    have hnat : (987591849 : ℕ)^137*625000000000^105 ≤ 75303559913^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987591849 5000000000 75303559913 625000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623603499/5000000000 : ℝ)^137 ≤ (43109499523441/100000000000000 : ℝ)^105 := by
    have hnat : (2623603499 : ℕ)^137*100000000000000^105 ≤ 43109499523441^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623603499 5000000000 43109499523441 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408075119/10000000000 : ℝ)^137 ≤ (4484193087291/10000000000000 : ℝ)^105 := by
    have hnat : (5408075119 : ℕ)^137*10000000000000^105 ≤ 4484193087291^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408075119 10000000000 4484193087291 10000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987591849/5000000000 : ℝ), (2623603499/5000000000 : ℝ), (5408075119/10000000000 : ℝ)] ![(75303559913/625000000000 : ℝ), (43109499523441/100000000000000 : ℝ), (4484193087291/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987591849/5000000000 : ℝ)|^137 ≤ (75303559913/625000000000 : ℝ)^105
        have hw : |(-987591849/5000000000 : ℝ)|=(987591849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623603499/5000000000 : ℝ)|^137 ≤ (43109499523441/100000000000000 : ℝ)^105
        have hw : |(2623603499/5000000000 : ℝ)|=(2623603499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408075119/10000000000 : ℝ)|^137 ≤ (4484193087291/10000000000000 : ℝ)^105
        have hw : |(5408075119/10000000000 : ℝ)|=(5408075119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_5 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305374609/10000000000 : ℝ)*x 0 + (-948111787/5000000000 : ℝ)*x 1 + (2704037557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305374609/10000000000 : ℝ)^137 ≤ (8746815999309/20000000000000 : ℝ)^105 := by
    have hnat : (5305374609 : ℕ)^137*20000000000000^105 ≤ 8746815999309^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305374609 10000000000 8746815999309 20000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948111787/5000000000 : ℝ)^137 ≤ (11423989168521/100000000000000 : ℝ)^105 := by
    have hnat : (948111787 : ℕ)^137*100000000000000^105 ≤ 11423989168521^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948111787 5000000000 11423989168521 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704037557/5000000000 : ℝ)^137 ≤ (44841930818817/100000000000000 : ℝ)^105 := by
    have hnat : (2704037557 : ℕ)^137*100000000000000^105 ≤ 44841930818817^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704037557 5000000000 44841930818817 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305374609/10000000000 : ℝ), (-948111787/5000000000 : ℝ), (2704037557/5000000000 : ℝ)] ![(8746815999309/20000000000000 : ℝ), (11423989168521/100000000000000 : ℝ), (44841930818817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305374609/10000000000 : ℝ)|^137 ≤ (8746815999309/20000000000000 : ℝ)^105
        have hw : |(5305374609/10000000000 : ℝ)|=(5305374609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948111787/5000000000 : ℝ)|^137 ≤ (11423989168521/100000000000000 : ℝ)^105
        have hw : |(-948111787/5000000000 : ℝ)|=(948111787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704037557/5000000000 : ℝ)|^137 ≤ (44841930818817/100000000000000 : ℝ)^105
        have hw : |(2704037557/5000000000 : ℝ)|=(2704037557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_6 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1326343653/2500000000 : ℝ)*x 0 + (2704037547/5000000000 : ℝ)*x 1 + (-1896223597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326343653/2500000000 : ℝ)^137 ≤ (10933520007203/25000000000000 : ℝ)^105 := by
    have hnat : (1326343653 : ℕ)^137*25000000000000^105 ≤ 10933520007203^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326343653 2500000000 10933520007203 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704037547/5000000000 : ℝ)^137 ≤ (11210482650611/25000000000000 : ℝ)^105 := by
    have hnat : (2704037547 : ℕ)^137*25000000000000^105 ≤ 11210482650611^105*5000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704037547 5000000000 11210482650611 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896223597/10000000000 : ℝ)^137 ≤ (2855997337329/25000000000000 : ℝ)^105 := by
    have hnat : (1896223597 : ℕ)^137*25000000000000^105 ≤ 2855997337329^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896223597 10000000000 2855997337329 25000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326343653/2500000000 : ℝ), (2704037547/5000000000 : ℝ), (-1896223597/10000000000 : ℝ)] ![(10933520007203/25000000000000 : ℝ), (11210482650611/25000000000000 : ℝ), (2855997337329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326343653/2500000000 : ℝ)|^137 ≤ (10933520007203/25000000000000 : ℝ)^105
        have hw : |(1326343653/2500000000 : ℝ)|=(1326343653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704037547/5000000000 : ℝ)|^137 ≤ (11210482650611/25000000000000 : ℝ)^105
        have hw : |(2704037547/5000000000 : ℝ)|=(2704037547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896223597/10000000000 : ℝ)|^137 ≤ (2855997337329/25000000000000 : ℝ)^105
        have hw : |(-1896223597/10000000000 : ℝ)|=(1896223597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1424_s5_7 (p : ℝ) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4305637209/10000000000 : ℝ)*x 0 + (4482506941/10000000000 : ℝ)*x 1 + (1033783253/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305637209/10000000000 : ℝ)^137 ≤ (33304735181091/100000000000000 : ℝ)^105 := by
    have hnat : (4305637209 : ℕ)^137*100000000000000^105 ≤ 33304735181091^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305637209 10000000000 33304735181091 100000000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482506941/10000000000 : ℝ)^137 ≤ (2193804158273/6250000000000 : ℝ)^105 := by
    have hnat : (4482506941 : ℕ)^137*6250000000000^105 ≤ 2193804158273^105*10000000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482506941 10000000000 2193804158273 6250000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033783253/2500000000 : ℝ)^137 ≤ (50551037221/160000000000 : ℝ)^105 := by
    have hnat : (1033783253 : ℕ)^137*160000000000^105 ≤ 50551037221^105*2500000000^137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033783253 2500000000 50551037221 160000000000 137 105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (137/32 : ℝ)) 137 105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305637209/10000000000 : ℝ), (4482506941/10000000000 : ℝ), (1033783253/2500000000 : ℝ)] ![(33304735181091/100000000000000 : ℝ), (2193804158273/6250000000000 : ℝ), (50551037221/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305637209/10000000000 : ℝ)|^137 ≤ (33304735181091/100000000000000 : ℝ)^105
        have hw : |(4305637209/10000000000 : ℝ)|=(4305637209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482506941/10000000000 : ℝ)|^137 ≤ (2193804158273/6250000000000 : ℝ)^105
        have hw : |(4482506941/10000000000 : ℝ)|=(4482506941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033783253/2500000000 : ℝ)|^137 ≤ (50551037221/160000000000 : ℝ)^105
        have hw : |(1033783253/2500000000 : ℝ)|=(1033783253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1424_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (462/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5663/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (462/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (462/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5651/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (462/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (462/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5651/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (462/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (462/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5651/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5651/50000 : ℝ) ^ (4383/1024 : ℝ) ≤ (4428083463573781/50000000000000000000 : ℝ) := by
    have hpowers : (5651/50000 : ℝ)^4383 ≤ (4428083463573781/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5651 : ℕ)^4383*50000000000000000000^1024 ≤ 4428083463573781^1024*50000^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5651 50000 4428083463573781 50000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5651/50000 : ℝ)) (X := (4428083463573781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (462/3125 : ℝ) ^ (4383/1024 : ℝ) ≤ (27956484124518259/100000000000000000000 : ℝ) := by
    have hpowers : (462/3125 : ℝ)^4383 ≤ (27956484124518259/100000000000000000000 : ℝ)^1024 := by
      have hnat : (462 : ℕ)^4383*100000000000000000000^1024 ≤ 27956484124518259^1024*3125^4383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        462 3125 27956484124518259 100000000000000000000 4383 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (462/3125 : ℝ)) (X := (27956484124518259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004428083463573781/25000000000000000000 : ℝ) ≤ (10000413785055657/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (25004428083463573781/25000000000000000000 : ℝ)^1024 ≤ (10000413785055657/10000000000000000 : ℝ)^4383 := by
      have hnat : (25004428083463573781 : ℕ)^1024*10000000000000000^4383 ≤ 10000413785055657^4383*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004428083463573781 25000000000000000000 10000413785055657 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000413785055657/10000000000000000 : ℝ)) (X := (25004428083463573781/25000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036812651051665821/100000000000000000000 : ℝ) ≤ (2500214983107393/2500000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (100036812651051665821/100000000000000000000 : ℝ)^1024 ≤ (2500214983107393/2500000000000000 : ℝ)^4383 := by
      have hnat : (100036812651051665821 : ℕ)^1024*2500000000000000^4383 ≤ 2500214983107393^4383*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036812651051665821 100000000000000000000 2500214983107393 2500000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500214983107393/2500000000000000 : ℝ)) (X := (100036812651051665821/100000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027956484124518259/50000000000000000000 : ℝ) ≤ (10001306079803487/10000000000000000 : ℝ) ^ (4383/1024 : ℝ) := by
    have hpowers : (50027956484124518259/50000000000000000000 : ℝ)^1024 ≤ (10001306079803487/10000000000000000 : ℝ)^4383 := by
      have hnat : (50027956484124518259 : ℕ)^1024*10000000000000000^4383 ≤ 10001306079803487^4383*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027956484124518259 50000000000000000000 10001306079803487 10000000000000000 1024 4383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001306079803487/10000000000000000 : ℝ)) (X := (50027956484124518259/50000000000000000000 : ℝ)) (by norm_num) 4383 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4428083463573781/50000000000000000000 : ℝ) ≤ ((17405678042161911507/17410000000000000000 : ℝ)+2*(89229474783/69640000000000 : ℝ)*(5651/50000 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (17405678042161911507/17410000000000000000 : ℝ)+2*(89229474783/69640000000000 : ℝ)*(5651/50000 : ℝ)=(10000413785055657/10000000000000000 : ℝ) by norm_num, show 1+2*(4428083463573781/50000000000000000000 : ℝ)=(25004428083463573781/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27956484124518259/100000000000000000000 : ℝ)+(4428083463573781/50000000000000000000 : ℝ) ≤ ((17405678042161911507/17410000000000000000 : ℝ)+(89229474783/69640000000000 : ℝ)*((462/3125 : ℝ)+(5651/50000 : ℝ)))^(4383/1024 : ℝ) := by
    rw [show (17405678042161911507/17410000000000000000 : ℝ)+(89229474783/69640000000000 : ℝ)*((462/3125 : ℝ)+(5651/50000 : ℝ))=(2500214983107393/2500000000000000 : ℝ) by norm_num, show 1+(27956484124518259/100000000000000000000 : ℝ)+(4428083463573781/50000000000000000000 : ℝ)=(100036812651051665821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27956484124518259/100000000000000000000 : ℝ) ≤ ((17405678042161911507/17410000000000000000 : ℝ)+2*(89229474783/69640000000000 : ℝ)*(462/3125 : ℝ))^(4383/1024 : ℝ) := by
    rw [show (17405678042161911507/17410000000000000000 : ℝ)+2*(89229474783/69640000000000 : ℝ)*(462/3125 : ℝ)=(10001306079803487/10000000000000000 : ℝ) by norm_num, show 1+2*(27956484124518259/100000000000000000000 : ℝ)=(50027956484124518259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17405678042161911507/17410000000000000000 : ℝ)*(X 1 0+X 2 0)+(89229474783/69640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (17405678042161911507/17410000000000000000 : ℝ)) (alpha := (89229474783/69640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17405678042161911507/17410000000000000000 : ℝ)*(X 0 1+X 2 1)+(89229474783/69640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (17405678042161911507/17410000000000000000 : ℝ)) (alpha := (89229474783/69640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17405678042161911507/17410000000000000000 : ℝ)*(X 0 2+X 1 2)+(89229474783/69640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4383/1024 : ℝ)) (lo := (5651/50000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (17405678042161911507/17410000000000000000 : ℝ)) (alpha := (89229474783/69640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1975172183/10000000000 : ℝ)*X 0 0+(2704331821/5000000000 : ℝ)*X 0 1+(5246621563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347480461/10000000000 : ℝ)*X 1 0+(-1028838521/5000000000 : ℝ)*X 1 1+(1311655413/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8555969/16000000 : ℝ)*X 2 0+(5246621549/10000000000 : ℝ)*X 2 1+(-12860481/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152806341/5000000000 : ℝ)*X 0 0+(516732767/1250000000 : ℝ)*X 0 1+(70058923/156250000 : ℝ)*X 0 2+(2152806341/5000000000 : ℝ)*X 1 0+(516732767/1250000000 : ℝ)*X 1 1+(70058923/156250000 : ℝ)*X 1 2+(2152806341/5000000000 : ℝ)*X 2 0+(516732767/1250000000 : ℝ)*X 2 1+(70058923/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-987591849/5000000000 : ℝ)*X 0 0+(2623603499/5000000000 : ℝ)*X 0 1+(5408075119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305374609/10000000000 : ℝ)*X 1 0+(-948111787/5000000000 : ℝ)*X 1 1+(2704037557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326343653/2500000000 : ℝ)*X 2 0+(2704037547/5000000000 : ℝ)*X 2 1+(-1896223597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305637209/10000000000 : ℝ)*X 0 0+(4482506941/10000000000 : ℝ)*X 0 1+(1033783253/2500000000 : ℝ)*X 0 2+(4305637209/10000000000 : ℝ)*X 1 0+(4482506941/10000000000 : ℝ)*X 1 1+(1033783253/2500000000 : ℝ)*X 1 2+(4305637209/10000000000 : ℝ)*X 2 0+(4482506941/10000000000 : ℝ)*X 2 1+(1033783253/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1424_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5825936417048445310270607049/870500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277920403/20000000000000 : ℝ)*(base19) + (1379777303/100000000000000 : ℝ)*(base23) + (106463057/100000000000000 : ℝ)*(lower2) + (164828697/100000000000000 : ℝ)*(upper3) + (77943979/50000000000000 : ℝ)*(upper5) + (451460789371317/10000000000000 : ℝ)*(major0) + (451460789371317/10000000000000 : ℝ)*(major1) + (4514607893713171/100000000000000 : ℝ)*(major2) + (1234253348921841/20000000000000 : ℝ)*(sp0) + (771412432415279/12500000000000 : ℝ)*(sp1) + (96426554205421/1562500000000 : ℝ)*(sp2) + (1428949848210117/50000000000000 : ℝ)*(sp3) + (17052157521/50000000000000 : ℝ)*(sp4) + (1501899411/10000000000000 : ℝ)*(sp7) + (357239339426793/12500000000000 : ℝ)*(f.failure) + (6171300848924247/100000000000000 : ℝ)*(f.sum) + (6089894326579/1392800000000000000000000000 : ℝ)*base65 + (635667306035630281/174100000000000000000000000000000 : ℝ)*base68 + (296406726848858697/1741000000000000000000000000000000 : ℝ)*base69 + (2006685597582630281/174100000000000000000000000000000 : ℝ)*base72 + (6910713994243/6964000000000000000000000000 : ℝ)*base73 + (4618892146257858697/1741000000000000000000000000000000 : ℝ)*base75 + (1729494721909005281/174100000000000000000000000000000 : ℝ)*base78 + (2392270268698205281/174100000000000000000000000000000 : ℝ)*base80 + (9343764301407/1741000000000000000000000000 : ℝ)*base81 + (7126593/1250000000000000000000 : ℝ)*base89 + (7126593/1250000000000000000000 : ℝ)*base91 + (5373407/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1458556063694228038583834163/435250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146093841/25000000000000 : ℝ)*(base19) + (149042799/25000000000000 : ℝ)*(base23) + (1553773/12500000000000 : ℝ)*(upper2) + (1554683/2500000000000 : ℝ)*(upper3) + (109973789/100000000000000 : ℝ)*(upper5) + (2273753755758603/50000000000000 : ℝ)*(major0) + (2273753755758603/50000000000000 : ℝ)*(major1) + (2273753755758603/50000000000000 : ℝ)*(major2) + (6288044823/50000000000000 : ℝ)*(sp1) + (10667303223/100000000000000 : ℝ)*(sp2) + (777034189270239/12500000000000 : ℝ)*(sp4) + (3108130176848451/50000000000000 : ℝ)*(sp5) + (1554065562671873/25000000000000 : ℝ)*(sp6) + (1439370698584969/50000000000000 : ℝ)*(sp7) + (1439370698584969/50000000000000 : ℝ)*(f.failure) + (777034189270239/12500000000000 : ℝ)*(f.sum) + (772434004843/1741000000000000000000000000 : ℝ)*base65 + (909224492119805279/870500000000000000000000000000000 : ℝ)*base68 + (1854118249094805279/870500000000000000000000000000000 : ℝ)*base70 + (553878846625805279/870500000000000000000000000000000 : ℝ)*base72 + (6211052829651/1741000000000000000000000000 : ℝ)*base73 + (429164520619194721/870500000000000000000000000000000 : ℝ)*base75 + (12788153344846694721/870500000000000000000000000000000 : ℝ)*base77 + (3189948854499305279/870500000000000000000000000000000 : ℝ)*base80 + (4902686260783/1741000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (67441631/5000000000000000000000 : ℝ)*base90 + (67441631/5000000000000000000000 : ℝ)*base92 + (67441631/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1424_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (462/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5651/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1424_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1424_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1424_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1424_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1424_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4383/1024 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157968601/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3163/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (517/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5663/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1424_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
