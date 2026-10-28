-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:39.012218+00:00
-- url     : https://prove2.me/submissions/51f96601-70da-4f45-9692-a887186b24c6

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
theorem support_rectangle_w1217_s3_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128467001/10000000000 : ℝ)*x 0 + (2710951643/5000000000 : ℝ)*x 1 + (5238636309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128467001/10000000000 : ℝ)^4205 ≤ (12934928663117/100000000000000 : ℝ)^3181 := by
    have hnat : (2128467001 : ℕ)^4205*100000000000000^3181 ≤ 12934928663117^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128467001 10000000000 12934928663117 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710951643/5000000000 : ℝ)^4205 ≤ (5565218448861/12500000000000 : ℝ)^3181 := by
    have hnat : (2710951643 : ℕ)^4205*12500000000000^3181 ≤ 5565218448861^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710951643 5000000000 5565218448861 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238636309/10000000000 : ℝ)^4205 ≤ (42543323729717/100000000000000 : ℝ)^3181 := by
    have hnat : (5238636309 : ℕ)^4205*100000000000000^3181 ≤ 42543323729717^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238636309 10000000000 42543323729717 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128467001/10000000000 : ℝ), (2710951643/5000000000 : ℝ), (5238636309/10000000000 : ℝ)] ![(12934928663117/100000000000000 : ℝ), (5565218448861/12500000000000 : ℝ), (42543323729717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128467001/10000000000 : ℝ)|^4205 ≤ (12934928663117/100000000000000 : ℝ)^3181
        have hw : |(-2128467001/10000000000 : ℝ)|=(2128467001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710951643/5000000000 : ℝ)|^4205 ≤ (5565218448861/12500000000000 : ℝ)^3181
        have hw : |(2710951643/5000000000 : ℝ)|=(2710951643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238636309/10000000000 : ℝ)|^4205 ≤ (42543323729717/100000000000000 : ℝ)^3181
        have hw : |(5238636309/10000000000 : ℝ)|=(5238636309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352049759/10000000000 : ℝ)*x 0 + (-2222002707/10000000000 : ℝ)*x 1 + (5238636109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352049759/10000000000 : ℝ)^4205 ≤ (875301537057/2000000000000 : ℝ)^3181 := by
    have hnat : (5352049759 : ℕ)^4205*2000000000000^3181 ≤ 875301537057^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352049759 10000000000 875301537057 2000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222002707/10000000000 : ℝ)^4205 ≤ (2738320308247/20000000000000 : ℝ)^3181 := by
    have hnat : (2222002707 : ℕ)^4205*20000000000000^3181 ≤ 2738320308247^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222002707 10000000000 2738320308247 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238636109/10000000000 : ℝ)^4205 ≤ (850866431653/2000000000000 : ℝ)^3181 := by
    have hnat : (5238636109 : ℕ)^4205*2000000000000^3181 ≤ 850866431653^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238636109 10000000000 850866431653 2000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352049759/10000000000 : ℝ), (-2222002707/10000000000 : ℝ), (5238636109/10000000000 : ℝ)] ![(875301537057/2000000000000 : ℝ), (2738320308247/20000000000000 : ℝ), (850866431653/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352049759/10000000000 : ℝ)|^4205 ≤ (875301537057/2000000000000 : ℝ)^3181
        have hw : |(5352049759/10000000000 : ℝ)|=(5352049759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222002707/10000000000 : ℝ)|^4205 ≤ (2738320308247/20000000000000 : ℝ)^3181
        have hw : |(-2222002707/10000000000 : ℝ)|=(2222002707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238636109/10000000000 : ℝ)|^4205 ≤ (850866431653/2000000000000 : ℝ)^3181
        have hw : |(5238636109/10000000000 : ℝ)|=(5238636109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352049857/10000000000 : ℝ)*x 0 + (5238635997/10000000000 : ℝ)*x 1 + (-1111001363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352049857/10000000000 : ℝ)^4205 ≤ (341914671189/781250000000 : ℝ)^3181 := by
    have hnat : (5352049857 : ℕ)^4205*781250000000^3181 ≤ 341914671189^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352049857 10000000000 341914671189 781250000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238635997/10000000000 : ℝ)^4205 ≤ (42543320380293/100000000000000 : ℝ)^3181 := by
    have hnat : (5238635997 : ℕ)^4205*100000000000000^3181 ≤ 42543320380293^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238635997 10000000000 42543320380293 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111001363/5000000000 : ℝ)^4205 ≤ (13691601695997/100000000000000 : ℝ)^3181 := by
    have hnat : (1111001363 : ℕ)^4205*100000000000000^3181 ≤ 13691601695997^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111001363 5000000000 13691601695997 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352049857/10000000000 : ℝ), (5238635997/10000000000 : ℝ), (-1111001363/5000000000 : ℝ)] ![(341914671189/781250000000 : ℝ), (42543320380293/100000000000000 : ℝ), (13691601695997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352049857/10000000000 : ℝ)|^4205 ≤ (341914671189/781250000000 : ℝ)^3181
        have hw : |(5352049857/10000000000 : ℝ)|=(5352049857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238635997/10000000000 : ℝ)|^4205 ≤ (42543320380293/100000000000000 : ℝ)^3181
        have hw : |(5238635997/10000000000 : ℝ)|=(5238635997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111001363/5000000000 : ℝ)|^4205 ≤ (13691601695997/100000000000000 : ℝ)^3181
        have hw : |(-1111001363/5000000000 : ℝ)|=(1111001363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2176194437/5000000000 : ℝ)*x 0 + (1042810099/2500000000 : ℝ)*x 1 + (4541216937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176194437/5000000000 : ℝ)^4205 ≤ (8324727840129/25000000000000 : ℝ)^3181 := by
    have hnat : (2176194437 : ℕ)^4205*25000000000000^3181 ≤ 8324727840129^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176194437 5000000000 8324727840129 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042810099/2500000000 : ℝ)^4205 ≤ (3147924332001/10000000000000 : ℝ)^3181 := by
    have hnat : (1042810099 : ℕ)^4205*10000000000000^3181 ≤ 3147924332001^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042810099 2500000000 3147924332001 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541216937/10000000000 : ℝ)^4205 ≤ (35221845299137/100000000000000 : ℝ)^3181 := by
    have hnat : (4541216937 : ℕ)^4205*100000000000000^3181 ≤ 35221845299137^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541216937 10000000000 35221845299137 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176194437/5000000000 : ℝ), (1042810099/2500000000 : ℝ), (4541216937/10000000000 : ℝ)] ![(8324727840129/25000000000000 : ℝ), (3147924332001/10000000000000 : ℝ), (35221845299137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176194437/5000000000 : ℝ)|^4205 ≤ (8324727840129/25000000000000 : ℝ)^3181
        have hw : |(2176194437/5000000000 : ℝ)|=(2176194437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042810099/2500000000 : ℝ)|^4205 ≤ (3147924332001/10000000000000 : ℝ)^3181
        have hw : |(1042810099/2500000000 : ℝ)|=(1042810099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541216937/10000000000 : ℝ)|^4205 ≤ (35221845299137/100000000000000 : ℝ)^3181
        have hw : |(4541216937/10000000000 : ℝ)|=(4541216937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128481833/10000000000 : ℝ)*x 0 + (130982817/250000000 : ℝ)*x 1 + (1355305839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128481833/10000000000 : ℝ)^4205 ≤ (6467523907327/50000000000000 : ℝ)^3181 := by
    have hnat : (2128481833 : ℕ)^4205*50000000000000^3181 ≤ 6467523907327^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128481833 10000000000 6467523907327 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130982817/250000000 : ℝ)^4205 ≤ (42550584948163/100000000000000 : ℝ)^3181 := by
    have hnat : (130982817 : ℕ)^4205*100000000000000^3181 ≤ 42550584948163^3181*250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130982817 250000000 42550584948163 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355305839/2500000000 : ℝ)^4205 ≤ (44514367219697/100000000000000 : ℝ)^3181 := by
    have hnat : (1355305839 : ℕ)^4205*100000000000000^3181 ≤ 44514367219697^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355305839 2500000000 44514367219697 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128481833/10000000000 : ℝ), (130982817/250000000 : ℝ), (1355305839/2500000000 : ℝ)] ![(6467523907327/50000000000000 : ℝ), (42550584948163/100000000000000 : ℝ), (44514367219697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128481833/10000000000 : ℝ)|^4205 ≤ (6467523907327/50000000000000 : ℝ)^3181
        have hw : |(-2128481833/10000000000 : ℝ)|=(2128481833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130982817/250000000 : ℝ)|^4205 ≤ (42550584948163/100000000000000 : ℝ)^3181
        have hw : |(130982817/250000000 : ℝ)|=(130982817/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355305839/2500000000 : ℝ)|^4205 ≤ (44514367219697/100000000000000 : ℝ)^3181
        have hw : |(1355305839/2500000000 : ℝ)|=(1355305839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652686499/5000000000 : ℝ)*x 0 + (-2039415469/10000000000 : ℝ)*x 1 + (5421223153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652686499/5000000000 : ℝ)^4205 ≤ (43261229103649/100000000000000 : ℝ)^3181 := by
    have hnat : (2652686499 : ℕ)^4205*100000000000000^3181 ≤ 43261229103649^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652686499 5000000000 43261229103649 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039415469/10000000000 : ℝ)^4205 ≤ (12224405868819/100000000000000 : ℝ)^3181 := by
    have hnat : (2039415469 : ℕ)^4205*100000000000000^3181 ≤ 12224405868819^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039415469 10000000000 12224405868819 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421223153/10000000000 : ℝ)^4205 ≤ (44514365016257/100000000000000 : ℝ)^3181 := by
    have hnat : (5421223153 : ℕ)^4205*100000000000000^3181 ≤ 44514365016257^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421223153 10000000000 44514365016257 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652686499/5000000000 : ℝ), (-2039415469/10000000000 : ℝ), (5421223153/10000000000 : ℝ)] ![(43261229103649/100000000000000 : ℝ), (12224405868819/100000000000000 : ℝ), (44514365016257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652686499/5000000000 : ℝ)|^4205 ≤ (43261229103649/100000000000000 : ℝ)^3181
        have hw : |(2652686499/5000000000 : ℝ)|=(2652686499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039415469/10000000000 : ℝ)|^4205 ≤ (12224405868819/100000000000000 : ℝ)^3181
        have hw : |(-2039415469/10000000000 : ℝ)|=(2039415469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421223153/10000000000 : ℝ)|^4205 ≤ (44514365016257/100000000000000 : ℝ)^3181
        have hw : |(5421223153/10000000000 : ℝ)|=(5421223153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305372843/10000000000 : ℝ)*x 0 + (5421223339/10000000000 : ℝ)*x 1 + (-15932933/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305372843/10000000000 : ℝ)^4205 ≤ (21630613716439/50000000000000 : ℝ)^3181 := by
    have hnat : (5305372843 : ℕ)^4205*50000000000000^3181 ≤ 21630613716439^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305372843 10000000000 21630613716439 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421223339/10000000000 : ℝ)^4205 ≤ (44514367035173/100000000000000 : ℝ)^3181 := by
    have hnat : (5421223339 : ℕ)^4205*100000000000000^3181 ≤ 44514367035173^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421223339 10000000000 44514367035173 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15932933/78125000 : ℝ)^4205 ≤ (2444881102451/20000000000000 : ℝ)^3181 := by
    have hnat : (15932933 : ℕ)^4205*20000000000000^3181 ≤ 2444881102451^3181*78125000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15932933 78125000 2444881102451 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305372843/10000000000 : ℝ), (5421223339/10000000000 : ℝ), (-15932933/78125000 : ℝ)] ![(21630613716439/50000000000000 : ℝ), (44514367035173/100000000000000 : ℝ), (2444881102451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305372843/10000000000 : ℝ)|^4205 ≤ (21630613716439/50000000000000 : ℝ)^3181
        have hw : |(5305372843/10000000000 : ℝ)|=(5305372843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421223339/10000000000 : ℝ)|^4205 ≤ (44514367035173/100000000000000 : ℝ)^3181
        have hw : |(5421223339/10000000000 : ℝ)|=(5421223339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15932933/78125000 : ℝ)|^4205 ≤ (2444881102451/20000000000000 : ℝ)^3181
        have hw : |(-15932933/78125000 : ℝ)|=(15932933/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s3_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1088104723/2500000000 : ℝ)*x 0 + (4539851079/10000000000 : ℝ)*x 1 + (1043153391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088104723/2500000000 : ℝ)^4205 ≤ (3329921495013/10000000000000 : ℝ)^3181 := by
    have hnat : (1088104723 : ℕ)^4205*10000000000000^3181 ≤ 3329921495013^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088104723 2500000000 3329921495013 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539851079/10000000000 : ℝ)^4205 ≤ (35207842117837/100000000000000 : ℝ)^3181 := by
    have hnat : (4539851079 : ℕ)^4205*100000000000000^3181 ≤ 35207842117837^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539851079 10000000000 35207842117837 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043153391/2500000000 : ℝ)^4205 ≤ (31492942926083/100000000000000 : ℝ)^3181 := by
    have hnat : (1043153391 : ℕ)^4205*100000000000000^3181 ≤ 31492942926083^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043153391 2500000000 31492942926083 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088104723/2500000000 : ℝ), (4539851079/10000000000 : ℝ), (1043153391/2500000000 : ℝ)] ![(3329921495013/10000000000000 : ℝ), (35207842117837/100000000000000 : ℝ), (31492942926083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088104723/2500000000 : ℝ)|^4205 ≤ (3329921495013/10000000000000 : ℝ)^3181
        have hw : |(1088104723/2500000000 : ℝ)|=(1088104723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539851079/10000000000 : ℝ)|^4205 ≤ (35207842117837/100000000000000 : ℝ)^3181
        have hw : |(4539851079/10000000000 : ℝ)|=(4539851079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043153391/2500000000 : ℝ)|^4205 ≤ (31492942926083/100000000000000 : ℝ)^3181
        have hw : |(1043153391/2500000000 : ℝ)|=(1043153391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5423/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (589/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1629/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2349/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1629/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2349/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1629/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2349/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1629/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2349/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1629/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2349/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1629/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2349/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2349/25000 : ℝ) ^ (8409/2048 : ℝ) ≤ (6066638580224939/100000000000000000000 : ℝ) := by
    have hpowers : (2349/25000 : ℝ)^8409 ≤ (6066638580224939/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2349 : ℕ)^8409*100000000000000000000^2048 ≤ 6066638580224939^2048*25000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2349 25000 6066638580224939 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2349/25000 : ℝ)) (X := (6066638580224939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1629/10000 : ℝ) ^ (8409/2048 : ℝ) ≤ (58100762892760693/100000000000000000000 : ℝ) := by
    have hpowers : (1629/10000 : ℝ)^8409 ≤ (58100762892760693/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1629 : ℕ)^8409*100000000000000000000^2048 ≤ 58100762892760693^2048*10000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1629 10000 58100762892760693 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1629/10000 : ℝ)) (X := (58100762892760693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006066638580224939/50000000000000000000 : ℝ) ≤ (5000147745340457/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50006066638580224939/50000000000000000000 : ℝ)^2048 ≤ (5000147745340457/5000000000000000 : ℝ)^8409 := by
      have hnat : (50006066638580224939 : ℕ)^2048*5000000000000000^8409 ≤ 5000147745340457^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006066638580224939 50000000000000000000 5000147745340457 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000147745340457/5000000000000000 : ℝ)) (X := (50006066638580224939/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127005231296030801/3125000000000000000 : ℝ) ≤ (6250976505501/6250000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (3127005231296030801/3125000000000000000 : ℝ)^2048 ≤ (6250976505501/6250000000000 : ℝ)^8409 := by
      have hnat : (3127005231296030801 : ℕ)^2048*6250000000000^8409 ≤ 6250976505501^8409*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127005231296030801 3125000000000000000 6250976505501 6250000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6250976505501/6250000000000 : ℝ)) (X := (3127005231296030801/3125000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058100762892760693/50000000000000000000 : ℝ) ≤ (5001414663461143/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50058100762892760693/50000000000000000000 : ℝ)^2048 ≤ (5001414663461143/5000000000000000 : ℝ)^8409 := by
      have hnat : (50058100762892760693 : ℕ)^2048*5000000000000000^8409 ≤ 5001414663461143^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058100762892760693 50000000000000000000 5001414663461143 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001414663461143/5000000000000000 : ℝ)) (X := (50058100762892760693/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6066638580224939/100000000000000000000 : ℝ) ≤ ((1914395255206396939/1915000000000000000 : ℝ)+2*(633459060343/344700000000000 : ℝ)*(2349/25000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (1914395255206396939/1915000000000000000 : ℝ)+2*(633459060343/344700000000000 : ℝ)*(2349/25000 : ℝ)=(5000147745340457/5000000000000000 : ℝ) by norm_num, show 1+2*(6066638580224939/100000000000000000000 : ℝ)=(50006066638580224939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58100762892760693/100000000000000000000 : ℝ)+(6066638580224939/100000000000000000000 : ℝ) ≤ ((1914395255206396939/1915000000000000000 : ℝ)+(633459060343/344700000000000 : ℝ)*((1629/10000 : ℝ)+(2349/25000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (1914395255206396939/1915000000000000000 : ℝ)+(633459060343/344700000000000 : ℝ)*((1629/10000 : ℝ)+(2349/25000 : ℝ))=(6250976505501/6250000000000 : ℝ) by norm_num, show 1+(58100762892760693/100000000000000000000 : ℝ)+(6066638580224939/100000000000000000000 : ℝ)=(3127005231296030801/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58100762892760693/100000000000000000000 : ℝ) ≤ ((1914395255206396939/1915000000000000000 : ℝ)+2*(633459060343/344700000000000 : ℝ)*(1629/10000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (1914395255206396939/1915000000000000000 : ℝ)+2*(633459060343/344700000000000 : ℝ)*(1629/10000 : ℝ)=(5001414663461143/5000000000000000 : ℝ) by norm_num, show 1+2*(58100762892760693/100000000000000000000 : ℝ)=(50058100762892760693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1914395255206396939/1915000000000000000 : ℝ)*(X 1 0+X 2 0)+(633459060343/344700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (2349/25000 : ℝ)) (hi := (1629/10000 : ℝ)) (c := (1914395255206396939/1915000000000000000 : ℝ)) (alpha := (633459060343/344700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1914395255206396939/1915000000000000000 : ℝ)*(X 0 1+X 2 1)+(633459060343/344700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (2349/25000 : ℝ)) (hi := (1629/10000 : ℝ)) (c := (1914395255206396939/1915000000000000000 : ℝ)) (alpha := (633459060343/344700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1914395255206396939/1915000000000000000 : ℝ)*(X 0 2+X 1 2)+(633459060343/344700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (2349/25000 : ℝ)) (hi := (1629/10000 : ℝ)) (c := (1914395255206396939/1915000000000000000 : ℝ)) (alpha := (633459060343/344700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128467001/10000000000 : ℝ)*X 0 0+(2710951643/5000000000 : ℝ)*X 0 1+(5238636309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352049759/10000000000 : ℝ)*X 1 0+(-2222002707/10000000000 : ℝ)*X 1 1+(5238636109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352049857/10000000000 : ℝ)*X 2 0+(5238635997/10000000000 : ℝ)*X 2 1+(-1111001363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176194437/5000000000 : ℝ)*X 0 0+(1042810099/2500000000 : ℝ)*X 0 1+(4541216937/10000000000 : ℝ)*X 0 2+(2176194437/5000000000 : ℝ)*X 1 0+(1042810099/2500000000 : ℝ)*X 1 1+(4541216937/10000000000 : ℝ)*X 1 2+(2176194437/5000000000 : ℝ)*X 2 0+(1042810099/2500000000 : ℝ)*X 2 1+(4541216937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128481833/10000000000 : ℝ)*X 0 0+(130982817/250000000 : ℝ)*X 0 1+(1355305839/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652686499/5000000000 : ℝ)*X 1 0+(-2039415469/10000000000 : ℝ)*X 1 1+(5421223153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305372843/10000000000 : ℝ)*X 2 0+(5421223339/10000000000 : ℝ)*X 2 1+(-15932933/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088104723/2500000000 : ℝ)*X 0 0+(4539851079/10000000000 : ℝ)*X 0 1+(1043153391/2500000000 : ℝ)*X 0 2+(1088104723/2500000000 : ℝ)*X 1 0+(4539851079/10000000000 : ℝ)*X 1 1+(1043153391/2500000000 : ℝ)*X 1 2+(1088104723/2500000000 : ℝ)*X 2 0+(4539851079/10000000000 : ℝ)*X 2 1+(1043153391/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8114295169767635694829437/2992187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (747429539/100000000000000 : ℝ)*(base19) + (51870219/6250000000000 : ℝ)*(base23) + (14567/156250000000 : ℝ)*(lower2) + (86160979/100000000000000 : ℝ)*(upper3) + (70635839/100000000000000 : ℝ)*(upper5) + (254981960970847/6250000000000 : ℝ)*(major0) + (254981960970847/6250000000000 : ℝ)*(major1) + (254981960970847/6250000000000 : ℝ)*(major2) + (5456528793078911/100000000000000 : ℝ)*(sp0) + (2728268420362029/50000000000000 : ℝ)*(sp1) + (1364134189557523/25000000000000 : ℝ)*(sp2) + (337859904166619/12500000000000 : ℝ)*(sp3) + (1759014937/20000000000000 : ℝ)*(sp4) + (2919593157/50000000000000 : ℝ)*(sp7) + (540577014503853/20000000000000 : ℝ)*(f.failure) + (1364134397038399/25000000000000 : ℝ)*(f.sum) + (11059421008159/4308750000000000000000000000 : ℝ)*base65 + (725371182397135997/107718750000000000000000000000000 : ℝ)*base67 + (545314129563645253/107718750000000000000000000000000 : ℝ)*base70 + (616831696954676503/107718750000000000000000000000000 : ℝ)*base72 + (2408817877277/2154375000000000000000000000 : ℝ)*base73 + (630486048578051503/107718750000000000000000000000000 : ℝ)*base76 + (303377826438010997/107718750000000000000000000000000 : ℝ)*base77 + (964102013258051503/107718750000000000000000000000000 : ℝ)*base80 + (4622423428093/2154375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (959/3906250000000000000 : ℝ)*base89 + (959/3906250000000000000 : ℝ)*base91 + (959/3906250000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59034147840439835161703/5745000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2309646383/100000000000000 : ℝ)*(base19) + (2305004977/100000000000000 : ℝ)*(base23) + (141974891/100000000000000 : ℝ)*(upper3) + (41722881/50000000000000 : ℝ)*(lower4) + (2243757/781250000000 : ℝ)*(upper5) + (2055059065181747/50000000000000 : ℝ)*(major0) + (2055059065181747/50000000000000 : ℝ)*(major1) + (2055059065181747/50000000000000 : ℝ)*(major2) + (44032005361/100000000000000 : ℝ)*(sp1) + (43881468641/100000000000000 : ℝ)*(sp2) + (687150725254297/12500000000000 : ℝ)*(sp4) + (687144932547829/12500000000000 : ℝ)*(sp5) + (5497159615560759/100000000000000 : ℝ)*(sp6) + (1361515058083907/50000000000000 : ℝ)*(sp7) + (1361515058083907/50000000000000 : ℝ)*(f.failure) + (687150725254297/12500000000000 : ℝ)*(f.sum) + (2533034700821/8617500000000000000000000000 : ℝ)*base65 + (6815282831689198103/861750000000000000000000000000000 : ℝ)*base68 + (72464339610301897/861750000000000000000000000000000 : ℝ)*base69 + (753457217776051897/861750000000000000000000000000000 : ℝ)*base71 + (30339339386243/17235000000000000000000000000 : ℝ)*base74 + (4236808143989551897/861750000000000000000000000000000 : ℝ)*base75 + (6865596343282198103/861750000000000000000000000000000 : ℝ)*base78 + (17380283281190698103/861750000000000000000000000000000 : ℝ)*base80 + (8337537888913/4308750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (148767/19531250000000000000 : ℝ)*base89 + (148767/19531250000000000000 : ℝ)*base91 + (148767/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5423/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (589/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_s4_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130918163/10000000000 : ℝ)*x 0 + (539852931/1000000000 : ℝ)*x 1 + (328775307/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130918163/10000000000 : ℝ)^4205 ≤ (12954623479413/100000000000000 : ℝ)^3181 := by
    have hnat : (2130918163 : ℕ)^4205*100000000000000^3181 ≤ 12954623479413^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130918163 10000000000 12954623479413 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539852931/1000000000 : ℝ)^4205 ≤ (44268203430537/100000000000000 : ℝ)^3181 := by
    have hnat : (539852931 : ℕ)^4205*100000000000000^3181 ≤ 44268203430537^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539852931 1000000000 44268203430537 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328775307/625000000 : ℝ)^4205 ≤ (21388586537871/50000000000000 : ℝ)^3181 := by
    have hnat : (328775307 : ℕ)^4205*50000000000000^3181 ≤ 21388586537871^3181*625000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328775307 625000000 21388586537871 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130918163/10000000000 : ℝ), (539852931/1000000000 : ℝ), (328775307/625000000 : ℝ)] ![(12954623479413/100000000000000 : ℝ), (44268203430537/100000000000000 : ℝ), (21388586537871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130918163/10000000000 : ℝ)|^4205 ≤ (12954623479413/100000000000000 : ℝ)^3181
        have hw : |(-2130918163/10000000000 : ℝ)|=(2130918163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539852931/1000000000 : ℝ)|^4205 ≤ (44268203430537/100000000000000 : ℝ)^3181
        have hw : |(539852931/1000000000 : ℝ)|=(539852931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328775307/625000000 : ℝ)|^4205 ≤ (21388586537871/50000000000000 : ℝ)^3181
        have hw : |(328775307/625000000 : ℝ)|=(328775307/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336542749/2500000000 : ℝ)*x 0 + (-2201061393/10000000000 : ℝ)*x 1 + (263020247/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336542749/2500000000 : ℝ)^4205 ≤ (21850770487939/50000000000000 : ℝ)^3181 := by
    have hnat : (1336542749 : ℕ)^4205*50000000000000^3181 ≤ 21850770487939^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336542749 2500000000 21850770487939 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201061393/10000000000 : ℝ)^4205 ≤ (13521285630189/100000000000000 : ℝ)^3181 := by
    have hnat : (2201061393 : ℕ)^4205*100000000000000^3181 ≤ 13521285630189^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201061393 10000000000 13521285630189 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263020247/500000000 : ℝ)^4205 ≤ (42777173376733/100000000000000 : ℝ)^3181 := by
    have hnat : (263020247 : ℕ)^4205*100000000000000^3181 ≤ 42777173376733^3181*500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263020247 500000000 42777173376733 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336542749/2500000000 : ℝ), (-2201061393/10000000000 : ℝ), (263020247/500000000 : ℝ)] ![(21850770487939/50000000000000 : ℝ), (13521285630189/100000000000000 : ℝ), (42777173376733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336542749/2500000000 : ℝ)|^4205 ≤ (21850770487939/50000000000000 : ℝ)^3181
        have hw : |(1336542749/2500000000 : ℝ)|=(1336542749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2201061393/10000000000 : ℝ)|^4205 ≤ (13521285630189/100000000000000 : ℝ)^3181
        have hw : |(-2201061393/10000000000 : ℝ)|=(2201061393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263020247/500000000 : ℝ)|^4205 ≤ (42777173376733/100000000000000 : ℝ)^3181
        have hw : |(263020247/500000000 : ℝ)|=(263020247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069234203/2000000000 : ℝ)*x 0 + (2630202467/5000000000 : ℝ)*x 1 + (-2149474/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069234203/2000000000 : ℝ)^4205 ≤ (10925385295297/25000000000000 : ℝ)^3181 := by
    have hnat : (1069234203 : ℕ)^4205*25000000000000^3181 ≤ 10925385295297^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069234203 2000000000 10925385295297 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630202467/5000000000 : ℝ)^4205 ≤ (8555434662447/20000000000000 : ℝ)^3181 := by
    have hnat : (2630202467 : ℕ)^4205*20000000000000^3181 ≤ 8555434662447^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630202467 5000000000 8555434662447 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2149474/9765625 : ℝ)^4205 ≤ (13521285492139/100000000000000 : ℝ)^3181 := by
    have hnat : (2149474 : ℕ)^4205*100000000000000^3181 ≤ 13521285492139^3181*9765625^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149474 9765625 13521285492139 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069234203/2000000000 : ℝ), (2630202467/5000000000 : ℝ), (-2149474/9765625 : ℝ)] ![(10925385295297/25000000000000 : ℝ), (8555434662447/20000000000000 : ℝ), (13521285492139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069234203/2000000000 : ℝ)|^4205 ≤ (10925385295297/25000000000000 : ℝ)^3181
        have hw : |(1069234203/2000000000 : ℝ)|=(1069234203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630202467/5000000000 : ℝ)|^4205 ≤ (8555434662447/20000000000000 : ℝ)^3181
        have hw : |(2630202467/5000000000 : ℝ)|=(2630202467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2149474/9765625 : ℝ)|^4205 ≤ (13521285492139/100000000000000 : ℝ)^3181
        have hw : |(-2149474/9765625 : ℝ)|=(2149474/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544232269/1250000000 : ℝ)*x 0 + (4216618913/10000000000 : ℝ)*x 1 + (1123865523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544232269/1250000000 : ℝ)^4205 ≤ (3331377182027/10000000000000 : ℝ)^3181 := by
    have hnat : (544232269 : ℕ)^4205*10000000000000^3181 ≤ 3331377182027^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544232269 1250000000 3331377182027 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216618913/10000000000 : ℝ)^4205 ≤ (7983183829999/25000000000000 : ℝ)^3181 := by
    have hnat : (4216618913 : ℕ)^4205*25000000000000^3181 ≤ 7983183829999^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216618913 10000000000 7983183829999 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123865523/2500000000 : ℝ)^4205 ≤ (8688373212833/25000000000000 : ℝ)^3181 := by
    have hnat : (1123865523 : ℕ)^4205*25000000000000^3181 ≤ 8688373212833^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123865523 2500000000 8688373212833 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544232269/1250000000 : ℝ), (4216618913/10000000000 : ℝ), (1123865523/2500000000 : ℝ)] ![(3331377182027/10000000000000 : ℝ), (7983183829999/25000000000000 : ℝ), (8688373212833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544232269/1250000000 : ℝ)|^4205 ≤ (3331377182027/10000000000000 : ℝ)^3181
        have hw : |(544232269/1250000000 : ℝ)|=(544232269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216618913/10000000000 : ℝ)|^4205 ≤ (7983183829999/25000000000000 : ℝ)^3181
        have hw : |(4216618913/10000000000 : ℝ)|=(4216618913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123865523/2500000000 : ℝ)|^4205 ≤ (8688373212833/25000000000000 : ℝ)^3181
        have hw : |(1123865523/2500000000 : ℝ)|=(1123865523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-532731007/2500000000 : ℝ)*x 0 + (5260789893/10000000000 : ℝ)*x 1 + (5398143171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532731007/2500000000 : ℝ)^4205 ≤ (12954670612791/100000000000000 : ℝ)^3181 := by
    have hnat : (532731007 : ℕ)^4205*100000000000000^3181 ≤ 12954670612791^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532731007 2500000000 12954670612791 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260789893/10000000000 : ℝ)^4205 ≤ (21390655772099/50000000000000 : ℝ)^3181 := by
    have hnat : (5260789893 : ℕ)^4205*50000000000000^3181 ≤ 21390655772099^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260789893 10000000000 21390655772099 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398143171/10000000000 : ℝ)^4205 ≤ (8852803566667/20000000000000 : ℝ)^3181 := by
    have hnat : (5398143171 : ℕ)^4205*20000000000000^3181 ≤ 8852803566667^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398143171 10000000000 8852803566667 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532731007/2500000000 : ℝ), (5260789893/10000000000 : ℝ), (5398143171/10000000000 : ℝ)] ![(12954670612791/100000000000000 : ℝ), (21390655772099/50000000000000 : ℝ), (8852803566667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532731007/2500000000 : ℝ)|^4205 ≤ (12954670612791/100000000000000 : ℝ)^3181
        have hw : |(-532731007/2500000000 : ℝ)|=(532731007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260789893/10000000000 : ℝ)|^4205 ≤ (21390655772099/50000000000000 : ℝ)^3181
        have hw : |(5260789893/10000000000 : ℝ)|=(5260789893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398143171/10000000000 : ℝ)|^4205 ≤ (8852803566667/20000000000000 : ℝ)^3181
        have hw : |(5398143171/10000000000 : ℝ)|=(5398143171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310989983/10000000000 : ℝ)*x 0 + (-82532939/400000000 : ℝ)*x 1 + (539814277/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310989983/10000000000 : ℝ)^4205 ≤ (43321785846859/100000000000000 : ℝ)^3181 := by
    have hnat : (5310989983 : ℕ)^4205*100000000000000^3181 ≤ 43321785846859^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310989983 10000000000 43321785846859 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82532939/400000000 : ℝ)^4205 ≤ (3103550162991/25000000000000 : ℝ)^3181 := by
    have hnat : (82532939 : ℕ)^4205*25000000000000^3181 ≤ 3103550162991^3181*400000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82532939 400000000 3103550162991 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539814277/1000000000 : ℝ)^4205 ≤ (44264013486701/100000000000000 : ℝ)^3181 := by
    have hnat : (539814277 : ℕ)^4205*100000000000000^3181 ≤ 44264013486701^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539814277 1000000000 44264013486701 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310989983/10000000000 : ℝ), (-82532939/400000000 : ℝ), (539814277/1000000000 : ℝ)] ![(43321785846859/100000000000000 : ℝ), (3103550162991/25000000000000 : ℝ), (44264013486701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310989983/10000000000 : ℝ)|^4205 ≤ (43321785846859/100000000000000 : ℝ)^3181
        have hw : |(5310989983/10000000000 : ℝ)|=(5310989983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82532939/400000000 : ℝ)|^4205 ≤ (3103550162991/25000000000000 : ℝ)^3181
        have hw : |(-82532939/400000000 : ℝ)|=(82532939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539814277/1000000000 : ℝ)|^4205 ≤ (44264013486701/100000000000000 : ℝ)^3181
        have hw : |(539814277/1000000000 : ℝ)|=(539814277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062198047/2000000000 : ℝ)*x 0 + (33738391/62500000 : ℝ)*x 1 + (-103166171/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062198047/2000000000 : ℝ)^4205 ≤ (8664357712827/20000000000000 : ℝ)^3181 := by
    have hnat : (1062198047 : ℕ)^4205*20000000000000^3181 ≤ 8664357712827^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062198047 2000000000 8664357712827 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33738391/62500000 : ℝ)^4205 ≤ (5533001401301/12500000000000 : ℝ)^3181 := by
    have hnat : (33738391 : ℕ)^4205*12500000000000^3181 ≤ 5533001401301^3181*62500000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33738391 62500000 5533001401301 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103166171/500000000 : ℝ)^4205 ≤ (6207100107263/50000000000000 : ℝ)^3181 := by
    have hnat : (103166171 : ℕ)^4205*50000000000000^3181 ≤ 6207100107263^3181*500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103166171 500000000 6207100107263 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062198047/2000000000 : ℝ), (33738391/62500000 : ℝ), (-103166171/500000000 : ℝ)] ![(8664357712827/20000000000000 : ℝ), (5533001401301/12500000000000 : ℝ), (6207100107263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062198047/2000000000 : ℝ)|^4205 ≤ (8664357712827/20000000000000 : ℝ)^3181
        have hw : |(1062198047/2000000000 : ℝ)|=(1062198047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33738391/62500000 : ℝ)|^4205 ≤ (5533001401301/12500000000000 : ℝ)^3181
        have hw : |(33738391/62500000 : ℝ)|=(33738391/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103166171/500000000 : ℝ)|^4205 ≤ (6207100107263/50000000000000 : ℝ)^3181
        have hw : |(-103166171/500000000 : ℝ)|=(103166171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s4_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4353870991/10000000000 : ℝ)*x 0 + (56183559/125000000 : ℝ)*x 1 + (2108699729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353870991/10000000000 : ℝ)^4205 ≤ (33313901682623/100000000000000 : ℝ)^3181 := by
    have hnat : (4353870991 : ℕ)^4205*100000000000000^3181 ≤ 33313901682623^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353870991 10000000000 33313901682623 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56183559/125000000 : ℝ)^4205 ≤ (34745548777791/100000000000000 : ℝ)^3181 := by
    have hnat : (56183559 : ℕ)^4205*100000000000000^3181 ≤ 34745548777791^3181*125000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56183559 125000000 34745548777791 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108699729/5000000000 : ℝ)^4205 ≤ (7985137382079/25000000000000 : ℝ)^3181 := by
    have hnat : (2108699729 : ℕ)^4205*25000000000000^3181 ≤ 7985137382079^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108699729 5000000000 7985137382079 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353870991/10000000000 : ℝ), (56183559/125000000 : ℝ), (2108699729/5000000000 : ℝ)] ![(33313901682623/100000000000000 : ℝ), (34745548777791/100000000000000 : ℝ), (7985137382079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353870991/10000000000 : ℝ)|^4205 ≤ (33313901682623/100000000000000 : ℝ)^3181
        have hw : |(4353870991/10000000000 : ℝ)|=(4353870991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56183559/125000000 : ℝ)|^4205 ≤ (34745548777791/100000000000000 : ℝ)^3181
        have hw : |(56183559/125000000 : ℝ)|=(56183559/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108699729/5000000000 : ℝ)|^4205 ≤ (7985137382079/25000000000000 : ℝ)^3181
        have hw : |(2108699729/5000000000 : ℝ)|=(2108699729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5423/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1131/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5423/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (589/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5423/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5423/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (589/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5423/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5423/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (589/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5423/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5423/50000 : ℝ) ^ (8409/2048 : ℝ) ≤ (2733999557492391/25000000000000000000 : ℝ) := by
    have hpowers : (5423/50000 : ℝ)^8409 ≤ (2733999557492391/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5423 : ℕ)^8409*25000000000000000000^2048 ≤ 2733999557492391^2048*50000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5423 50000 2733999557492391 25000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5423/50000 : ℝ)) (X := (2733999557492391/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (589/4000 : ℝ) ^ (8409/2048 : ℝ) ≤ (9594245614632091/25000000000000000000 : ℝ) := by
    have hpowers : (589/4000 : ℝ)^8409 ≤ (9594245614632091/25000000000000000000 : ℝ)^2048 := by
      have hnat : (589 : ℕ)^8409*25000000000000000000^2048 ≤ 9594245614632091^2048*4000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        589 4000 9594245614632091 25000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (589/4000 : ℝ)) (X := (9594245614632091/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502733999557492391/12500000000000000000 : ℝ) ≤ (10000532645304201/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (12502733999557492391/12500000000000000000 : ℝ)^2048 ≤ (10000532645304201/10000000000000000 : ℝ)^8409 := by
      have hnat : (12502733999557492391 : ℕ)^2048*10000000000000000^8409 ≤ 10000532645304201^8409*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502733999557492391 12500000000000000000 10000532645304201 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000532645304201/10000000000000000 : ℝ)) (X := (12502733999557492391/12500000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506164122586062241/12500000000000000000 : ℝ) ≤ (10001200786695727/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (12506164122586062241/12500000000000000000 : ℝ)^2048 ≤ (10001200786695727/10000000000000000 : ℝ)^8409 := by
      have hnat : (12506164122586062241 : ℕ)^2048*10000000000000000^8409 ≤ 10001200786695727^8409*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506164122586062241 12500000000000000000 10001200786695727 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001200786695727/10000000000000000 : ℝ)) (X := (12506164122586062241/12500000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509594245614632091/12500000000000000000 : ℝ) ≤ (10001868928087253/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (12509594245614632091/12500000000000000000 : ℝ)^2048 ≤ (10001868928087253/10000000000000000 : ℝ)^8409 := by
      have hnat : (12509594245614632091 : ℕ)^2048*10000000000000000^8409 ≤ 10001868928087253^8409*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509594245614632091 12500000000000000000 10001868928087253 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001868928087253/10000000000000000 : ℝ)) (X := (12509594245614632091/12500000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2733999557492391/25000000000000000000 : ℝ) ≤ ((38777572808070013687/38790000000000000000 : ℝ)+2*(334070695763/193950000000000 : ℝ)*(5423/50000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (38777572808070013687/38790000000000000000 : ℝ)+2*(334070695763/193950000000000 : ℝ)*(5423/50000 : ℝ)=(10000532645304201/10000000000000000 : ℝ) by norm_num, show 1+2*(2733999557492391/25000000000000000000 : ℝ)=(12502733999557492391/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9594245614632091/25000000000000000000 : ℝ)+(2733999557492391/25000000000000000000 : ℝ) ≤ ((38777572808070013687/38790000000000000000 : ℝ)+(334070695763/193950000000000 : ℝ)*((589/4000 : ℝ)+(5423/50000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (38777572808070013687/38790000000000000000 : ℝ)+(334070695763/193950000000000 : ℝ)*((589/4000 : ℝ)+(5423/50000 : ℝ))=(10001200786695727/10000000000000000 : ℝ) by norm_num, show 1+(9594245614632091/25000000000000000000 : ℝ)+(2733999557492391/25000000000000000000 : ℝ)=(12506164122586062241/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9594245614632091/25000000000000000000 : ℝ) ≤ ((38777572808070013687/38790000000000000000 : ℝ)+2*(334070695763/193950000000000 : ℝ)*(589/4000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (38777572808070013687/38790000000000000000 : ℝ)+2*(334070695763/193950000000000 : ℝ)*(589/4000 : ℝ)=(10001868928087253/10000000000000000 : ℝ) by norm_num, show 1+2*(9594245614632091/25000000000000000000 : ℝ)=(12509594245614632091/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38777572808070013687/38790000000000000000 : ℝ)*(X 1 0+X 2 0)+(334070695763/193950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (5423/50000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (38777572808070013687/38790000000000000000 : ℝ)) (alpha := (334070695763/193950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38777572808070013687/38790000000000000000 : ℝ)*(X 0 1+X 2 1)+(334070695763/193950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (5423/50000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (38777572808070013687/38790000000000000000 : ℝ)) (alpha := (334070695763/193950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38777572808070013687/38790000000000000000 : ℝ)*(X 0 2+X 1 2)+(334070695763/193950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (5423/50000 : ℝ)) (hi := (589/4000 : ℝ)) (c := (38777572808070013687/38790000000000000000 : ℝ)) (alpha := (334070695763/193950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130918163/10000000000 : ℝ)*X 0 0+(539852931/1000000000 : ℝ)*X 0 1+(328775307/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336542749/2500000000 : ℝ)*X 1 0+(-2201061393/10000000000 : ℝ)*X 1 1+(263020247/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069234203/2000000000 : ℝ)*X 2 0+(2630202467/5000000000 : ℝ)*X 2 1+(-2149474/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544232269/1250000000 : ℝ)*X 0 0+(4216618913/10000000000 : ℝ)*X 0 1+(1123865523/2500000000 : ℝ)*X 0 2+(544232269/1250000000 : ℝ)*X 1 0+(4216618913/10000000000 : ℝ)*X 1 1+(1123865523/2500000000 : ℝ)*X 1 2+(544232269/1250000000 : ℝ)*X 2 0+(4216618913/10000000000 : ℝ)*X 2 1+(1123865523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532731007/2500000000 : ℝ)*X 0 0+(5260789893/10000000000 : ℝ)*X 0 1+(5398143171/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310989983/10000000000 : ℝ)*X 1 0+(-82532939/400000000 : ℝ)*X 1 1+(539814277/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062198047/2000000000 : ℝ)*X 2 0+(33738391/62500000 : ℝ)*X 2 1+(-103166171/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353870991/10000000000 : ℝ)*X 0 0+(56183559/125000000 : ℝ)*X 0 1+(2108699729/5000000000 : ℝ)*X 0 2+(4353870991/10000000000 : ℝ)*X 1 0+(56183559/125000000 : ℝ)*X 1 1+(2108699729/5000000000 : ℝ)*X 1 2+(4353870991/10000000000 : ℝ)*X 2 0+(56183559/125000000 : ℝ)*X 2 1+(2108699729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1789656474315296216839/258600000000000000000000000 : ℝ) := by norm_num
    linear_combination (674641361/50000000000000 : ℝ)*(base19) + (1197509387/100000000000000 : ℝ)*(base23) + (9489647/10000000000000 : ℝ)*(lower2) + (174108103/100000000000000 : ℝ)*(upper3) + (71986411/100000000000000 : ℝ)*(upper5) + (1082620441587077/20000000000000 : ℝ)*(major0) + (1082620441587077/20000000000000 : ℝ)*(major1) + (1082620441587077/20000000000000 : ℝ)*(major2) + (7239887492934103/100000000000000 : ℝ)*(sp0) + (361996070196921/5000000000000 : ℝ)*(sp1) + (1809980388927939/25000000000000 : ℝ)*(sp2) + (896565446575859/25000000000000 : ℝ)*(sp3) + (110188397/312500000000 : ℝ)*(sp4) + (4911415223/25000000000000 : ℝ)*(sp7) + (448285178995541/12500000000000 : ℝ)*(f.failure) + (7239922753221143/100000000000000 : ℝ)*(f.sum) + (713133925963/3879000000000000000000000000 : ℝ)*base66 + (4549660376873877101/775800000000000000000000000000000 : ℝ)*base68 + (2372658102196677101/775800000000000000000000000000000 : ℝ)*base70 + (11329135040791322899/775800000000000000000000000000000 : ℝ)*base71 + (939686469649/387900000000000000000000000 : ℝ)*base74 + (15599154622584122899/775800000000000000000000000000000 : ℝ)*base75 + (1431134933524677101/775800000000000000000000000000000 : ℝ)*base78 + (11052252914512922899/775800000000000000000000000000000 : ℝ)*base79 + (650374778467/1939500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (190857/39062500000000000000 : ℝ)*base90 + (190857/39062500000000000000 : ℝ)*base92 + (190857/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (683437063287180800393/215500000000000000000000000 : ℝ) := by norm_num
    linear_combination (119716227/25000000000000 : ℝ)*(base23) + (174909323/100000000000000 : ℝ)*(lower2) + (292667209/100000000000000 : ℝ)*(lower3) + (253831199/100000000000000 : ℝ)*(lower4) + (1088690761311719/20000000000000 : ℝ)*(major0) + (1088690761311719/20000000000000 : ℝ)*(major1) + (1088690761311719/20000000000000 : ℝ)*(major2) + (924020521/25000000000000 : ℝ)*(sp0) + (1874127257/50000000000000 : ℝ)*(sp1) + (727742029/50000000000000 : ℝ)*(sp2) + (7280513877727157/100000000000000 : ℝ)*(sp4) + (3640256912777363/50000000000000 : ℝ)*(sp5) + (291220625578411/4000000000000 : ℝ)*(sp6) + (721277986718911/20000000000000 : ℝ)*(sp7) + (721277986718911/20000000000000 : ℝ)*(f.failure) + (182012939345231/2500000000000 : ℝ)*(f.sum) + (26875667629151/3879000000000000000000000000 : ℝ)*base65 + (329854599724902047/775800000000000000000000000000000 : ℝ)*base68 + (2435300787731897953/775800000000000000000000000000000 : ℝ)*base69 + (6412441844612297953/775800000000000000000000000000000 : ℝ)*base71 + (1177876439851/1939500000000000000000000000 : ℝ)*base73 + (2087255355123102047/775800000000000000000000000000000 : ℝ)*base76 + (7003008198777102047/775800000000000000000000000000000 : ℝ)*base78 + (1244057461805297953/775800000000000000000000000000000 : ℝ)*base79 + (1406691414479/969750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4691/7812500000000000000 : ℝ)*base89 + (4691/7812500000000000000 : ℝ)*base91 + (4691/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (589/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5423/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_s5_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131412621/10000000000 : ℝ)*x 0 + (2696507123/5000000000 : ℝ)*x 1 + (2632797389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131412621/10000000000 : ℝ)^4205 ≤ (2591719455839/20000000000000 : ℝ)^3181 := by
    have hnat : (2131412621 : ℕ)^4205*20000000000000^3181 ≤ 2591719455839^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131412621 10000000000 2591719455839 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696507123/5000000000 : ℝ)^4205 ≤ (44208431416799/100000000000000 : ℝ)^3181 := by
    have hnat : (2696507123 : ℕ)^4205*100000000000000^3181 ≤ 44208431416799^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696507123 5000000000 44208431416799 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632797389/5000000000 : ℝ)^4205 ≤ (334632588229/781250000000 : ℝ)^3181 := by
    have hnat : (2632797389 : ℕ)^4205*781250000000^3181 ≤ 334632588229^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632797389 5000000000 334632588229 781250000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131412621/10000000000 : ℝ), (2696507123/5000000000 : ℝ), (2632797389/5000000000 : ℝ)] ![(2591719455839/20000000000000 : ℝ), (44208431416799/100000000000000 : ℝ), (334632588229/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131412621/10000000000 : ℝ)|^4205 ≤ (2591719455839/20000000000000 : ℝ)^3181
        have hw : |(-2131412621/10000000000 : ℝ)|=(2131412621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696507123/5000000000 : ℝ)|^4205 ≤ (44208431416799/100000000000000 : ℝ)^3181
        have hw : |(2696507123/5000000000 : ℝ)|=(2696507123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632797389/5000000000 : ℝ)|^4205 ≤ (334632588229/781250000000 : ℝ)^3181
        have hw : |(2632797389/5000000000 : ℝ)|=(2632797389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336194401/2500000000 : ℝ)*x 0 + (-1098021227/5000000000 : ℝ)*x 1 + (658199347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336194401/2500000000 : ℝ)^4205 ≤ (21843242458073/50000000000000 : ℝ)^3181 := by
    have hnat : (1336194401 : ℕ)^4205*50000000000000^3181 ≤ 21843242458073^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336194401 2500000000 21843242458073 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098021227/5000000000 : ℝ)^4205 ≤ (10784435037/80000000000 : ℝ)^3181 := by
    have hnat : (1098021227 : ℕ)^4205*80000000000^3181 ≤ 10784435037^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098021227 5000000000 10784435037 80000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658199347/1250000000 : ℝ)^4205 ≤ (21416485635903/50000000000000 : ℝ)^3181 := by
    have hnat : (658199347 : ℕ)^4205*50000000000000^3181 ≤ 21416485635903^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658199347 1250000000 21416485635903 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336194401/2500000000 : ℝ), (-1098021227/5000000000 : ℝ), (658199347/1250000000 : ℝ)] ![(21843242458073/50000000000000 : ℝ), (10784435037/80000000000 : ℝ), (21416485635903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336194401/2500000000 : ℝ)|^4205 ≤ (21843242458073/50000000000000 : ℝ)^3181
        have hw : |(1336194401/2500000000 : ℝ)|=(1336194401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098021227/5000000000 : ℝ)|^4205 ≤ (10784435037/80000000000 : ℝ)^3181
        have hw : |(-1098021227/5000000000 : ℝ)|=(1098021227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658199347/1250000000 : ℝ)|^4205 ≤ (21416485635903/50000000000000 : ℝ)^3181
        have hw : |(658199347/1250000000 : ℝ)|=(658199347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068955521/2000000000 : ℝ)*x 0 + (1316398693/2500000000 : ℝ)*x 1 + (-2196042459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068955521/2000000000 : ℝ)^4205 ≤ (43686484926951/100000000000000 : ℝ)^3181 := by
    have hnat : (1068955521 : ℕ)^4205*100000000000000^3181 ≤ 43686484926951^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068955521 2000000000 43686484926951 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316398693/2500000000 : ℝ)^4205 ≤ (21416485614397/50000000000000 : ℝ)^3181 := by
    have hnat : (1316398693 : ℕ)^4205*50000000000000^3181 ≤ 21416485614397^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316398693 2500000000 21416485614397 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196042459/10000000000 : ℝ)^4205 ≤ (13480543836823/100000000000000 : ℝ)^3181 := by
    have hnat : (2196042459 : ℕ)^4205*100000000000000^3181 ≤ 13480543836823^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196042459 10000000000 13480543836823 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068955521/2000000000 : ℝ), (1316398693/2500000000 : ℝ), (-2196042459/10000000000 : ℝ)] ![(43686484926951/100000000000000 : ℝ), (21416485614397/50000000000000 : ℝ), (13480543836823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068955521/2000000000 : ℝ)|^4205 ≤ (43686484926951/100000000000000 : ℝ)^3181
        have hw : |(1068955521/2000000000 : ℝ)|=(1068955521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316398693/2500000000 : ℝ)|^4205 ≤ (21416485614397/50000000000000 : ℝ)^3181
        have hw : |(1316398693/2500000000 : ℝ)|=(1316398693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196042459/10000000000 : ℝ)|^4205 ≤ (13480543836823/100000000000000 : ℝ)^3181
        have hw : |(-2196042459/10000000000 : ℝ)|=(2196042459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4354146107/10000000000 : ℝ)*x 0 + (845477493/2000000000 : ℝ)*x 1 + (4484619693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354146107/10000000000 : ℝ)^4205 ≤ (832917110551/2500000000000 : ℝ)^3181 := by
    have hnat : (4354146107 : ℕ)^4205*2500000000000^3181 ≤ 832917110551^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354146107 10000000000 832917110551 2500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845477493/2000000000 : ℝ)^4205 ≤ (16020291373531/50000000000000 : ℝ)^3181 := by
    have hnat : (845477493 : ℕ)^4205*50000000000000^3181 ≤ 16020291373531^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845477493 2000000000 16020291373531 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484619693/10000000000 : ℝ)^4205 ≤ (6928546561591/20000000000000 : ℝ)^3181 := by
    have hnat : (4484619693 : ℕ)^4205*20000000000000^3181 ≤ 6928546561591^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484619693 10000000000 6928546561591 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354146107/10000000000 : ℝ), (845477493/2000000000 : ℝ), (4484619693/10000000000 : ℝ)] ![(832917110551/2500000000000 : ℝ), (16020291373531/50000000000000 : ℝ), (6928546561591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354146107/10000000000 : ℝ)|^4205 ≤ (832917110551/2500000000000 : ℝ)^3181
        have hw : |(4354146107/10000000000 : ℝ)|=(4354146107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845477493/2000000000 : ℝ)|^4205 ≤ (16020291373531/50000000000000 : ℝ)^3181
        have hw : |(845477493/2000000000 : ℝ)|=(845477493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484619693/10000000000 : ℝ)|^4205 ≤ (6928546561591/20000000000000 : ℝ)^3181
        have hw : |(4484619693/10000000000 : ℝ)|=(4484619693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-532854423/2500000000 : ℝ)*x 0 + (2632961297/5000000000 : ℝ)*x 1 + (215707407/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532854423/2500000000 : ℝ)^4205 ≤ (12958638034727/100000000000000 : ℝ)^3181 := by
    have hnat : (532854423 : ℕ)^4205*100000000000000^3181 ≤ 12958638034727^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532854423 2500000000 12958638034727 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632961297/5000000000 : ℝ)^4205 ≤ (4283649636211/10000000000000 : ℝ)^3181 := by
    have hnat : (2632961297 : ℕ)^4205*10000000000000^3181 ≤ 4283649636211^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632961297 5000000000 4283649636211 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215707407/400000000 : ℝ)^4205 ≤ (22102432791017/50000000000000 : ℝ)^3181 := by
    have hnat : (215707407 : ℕ)^4205*50000000000000^3181 ≤ 22102432791017^3181*400000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215707407 400000000 22102432791017 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532854423/2500000000 : ℝ), (2632961297/5000000000 : ℝ), (215707407/400000000 : ℝ)] ![(12958638034727/100000000000000 : ℝ), (4283649636211/10000000000000 : ℝ), (22102432791017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532854423/2500000000 : ℝ)|^4205 ≤ (12958638034727/100000000000000 : ℝ)^3181
        have hw : |(-532854423/2500000000 : ℝ)|=(532854423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632961297/5000000000 : ℝ)|^4205 ≤ (4283649636211/10000000000000 : ℝ)^3181
        have hw : |(2632961297/5000000000 : ℝ)|=(2632961297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215707407/400000000 : ℝ)|^4205 ≤ (22102432791017/50000000000000 : ℝ)^3181
        have hw : |(215707407/400000000 : ℝ)|=(215707407/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212492879/400000000 : ℝ)*x 0 + (-1034475931/5000000000 : ℝ)*x 1 + (1078537037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212492879/400000000 : ℝ)^4205 ≤ (8667229816903/20000000000000 : ℝ)^3181 := by
    have hnat : (212492879 : ℕ)^4205*20000000000000^3181 ≤ 8667229816903^3181*400000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212492879 400000000 8667229816903 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034475931/5000000000 : ℝ)^4205 ≤ (19467164383/156250000000 : ℝ)^3181 := by
    have hnat : (1034475931 : ℕ)^4205*156250000000^3181 ≤ 19467164383^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034475931 5000000000 19467164383 156250000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078537037/2000000000 : ℝ)^4205 ≤ (44204865690393/100000000000000 : ℝ)^3181 := by
    have hnat : (1078537037 : ℕ)^4205*100000000000000^3181 ≤ 44204865690393^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078537037 2000000000 44204865690393 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212492879/400000000 : ℝ), (-1034475931/5000000000 : ℝ), (1078537037/2000000000 : ℝ)] ![(8667229816903/20000000000000 : ℝ), (19467164383/156250000000 : ℝ), (44204865690393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212492879/400000000 : ℝ)|^4205 ≤ (8667229816903/20000000000000 : ℝ)^3181
        have hw : |(212492879/400000000 : ℝ)|=(212492879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1034475931/5000000000 : ℝ)|^4205 ≤ (19467164383/156250000000 : ℝ)^3181
        have hw : |(-1034475931/5000000000 : ℝ)|=(1034475931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078537037/2000000000 : ℝ)|^4205 ≤ (44204865690393/100000000000000 : ℝ)^3181
        have hw : |(1078537037/2000000000 : ℝ)|=(1078537037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328080453/2500000000 : ℝ)*x 0 + (5392685373/10000000000 : ℝ)*x 1 + (-2068951827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328080453/2500000000 : ℝ)^4205 ≤ (4333614732677/10000000000000 : ℝ)^3181 := by
    have hnat : (1328080453 : ℕ)^4205*10000000000000^3181 ≤ 4333614732677^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328080453 2500000000 4333614732677 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392685373/10000000000 : ℝ)^4205 ≤ (22102433863777/50000000000000 : ℝ)^3181 := by
    have hnat : (5392685373 : ℕ)^4205*50000000000000^3181 ≤ 22102433863777^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392685373 10000000000 22102433863777 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068951827/10000000000 : ℝ)^4205 ≤ (6229492463253/50000000000000 : ℝ)^3181 := by
    have hnat : (2068951827 : ℕ)^4205*50000000000000^3181 ≤ 6229492463253^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068951827 10000000000 6229492463253 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328080453/2500000000 : ℝ), (5392685373/10000000000 : ℝ), (-2068951827/10000000000 : ℝ)] ![(4333614732677/10000000000000 : ℝ), (22102433863777/50000000000000 : ℝ), (6229492463253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328080453/2500000000 : ℝ)|^4205 ≤ (4333614732677/10000000000000 : ℝ)^3181
        have hw : |(1328080453/2500000000 : ℝ)|=(1328080453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392685373/10000000000 : ℝ)|^4205 ≤ (22102433863777/50000000000000 : ℝ)^3181
        have hw : |(5392685373/10000000000 : ℝ)|=(5392685373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068951827/10000000000 : ℝ)|^4205 ≤ (6229492463253/50000000000000 : ℝ)^3181
        have hw : |(-2068951827/10000000000 : ℝ)|=(2068951827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s5_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177078229/5000000000 : ℝ)*x 0 + (2241978953/5000000000 : ℝ)*x 1 + (2114025737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177078229/5000000000 : ℝ)^4205 ≤ (33316789121293/100000000000000 : ℝ)^3181 := by
    have hnat : (2177078229 : ℕ)^4205*100000000000000^3181 ≤ 33316789121293^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177078229 5000000000 33316789121293 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241978953/5000000000 : ℝ)^4205 ≤ (17317987570599/50000000000000 : ℝ)^3181 := by
    have hnat : (2241978953 : ℕ)^4205*50000000000000^3181 ≤ 17317987570599^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241978953 5000000000 17317987570599 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114025737/5000000000 : ℝ)^4205 ≤ (8011808929503/25000000000000 : ℝ)^3181 := by
    have hnat : (2114025737 : ℕ)^4205*25000000000000^3181 ≤ 8011808929503^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114025737 5000000000 8011808929503 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177078229/5000000000 : ℝ), (2241978953/5000000000 : ℝ), (2114025737/5000000000 : ℝ)] ![(33316789121293/100000000000000 : ℝ), (17317987570599/50000000000000 : ℝ), (8011808929503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177078229/5000000000 : ℝ)|^4205 ≤ (33316789121293/100000000000000 : ℝ)^3181
        have hw : |(2177078229/5000000000 : ℝ)|=(2177078229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241978953/5000000000 : ℝ)|^4205 ≤ (17317987570599/50000000000000 : ℝ)^3181
        have hw : |(2241978953/5000000000 : ℝ)|=(2241978953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114025737/5000000000 : ℝ)|^4205 ≤ (8011808929503/25000000000000 : ℝ)^3181
        have hw : |(2114025737/5000000000 : ℝ)|=(2114025737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11421/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1131/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1131/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1131/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1131/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1131/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1131/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1131/10000 : ℝ) ^ (8409/2048 : ℝ) ≤ (12988473940557813/100000000000000000000 : ℝ) := by
    have hpowers : (1131/10000 : ℝ)^8409 ≤ (12988473940557813/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1131 : ℕ)^8409*100000000000000000000^2048 ≤ 12988473940557813^2048*10000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1131 10000 12988473940557813 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1131/10000 : ℝ)) (X := (12988473940557813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8409/2048 : ℝ) ≤ (8349532619952501/25000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8409 ≤ (8349532619952501/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8409*25000000000000000000^2048 ≤ 8349532619952501^2048*20000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 8349532619952501 25000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (8349532619952501/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012988473940557813/50000000000000000000 : ℝ) ≤ (2500158150680813/2500000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50012988473940557813/50000000000000000000 : ℝ)^2048 ≤ (2500158150680813/2500000000000000 : ℝ)^8409 := by
      have hnat : (50012988473940557813 : ℕ)^2048*2500000000000000^8409 ≤ 2500158150680813^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012988473940557813 50000000000000000000 2500158150680813 2500000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500158150680813/2500000000000000 : ℝ)) (X := (50012988473940557813/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046386604420367817/100000000000000000000 : ℝ) ≤ (10001129541004199/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100046386604420367817/100000000000000000000 : ℝ)^2048 ≤ (10001129541004199/10000000000000000 : ℝ)^8409 := by
      have hnat : (100046386604420367817 : ℕ)^2048*10000000000000000^8409 ≤ 10001129541004199^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046386604420367817 100000000000000000000 10001129541004199 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001129541004199/10000000000000000 : ℝ)) (X := (100046386604420367817/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508349532619952501/12500000000000000000 : ℝ) ≤ (5000813239642573/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (12508349532619952501/12500000000000000000 : ℝ)^2048 ≤ (5000813239642573/5000000000000000 : ℝ)^8409 := by
      have hnat : (12508349532619952501 : ℕ)^2048*5000000000000000^8409 ≤ 5000813239642573^8409*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508349532619952501 12500000000000000000 5000813239642573 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000813239642573/5000000000000000 : ℝ)) (X := (12508349532619952501/12500000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12988473940557813/100000000000000000000 : ℝ) ≤ ((3123996754172061/3125000000000000 : ℝ)+2*(165646093649/97500000000000 : ℝ)*(1131/10000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (3123996754172061/3125000000000000 : ℝ)+2*(165646093649/97500000000000 : ℝ)*(1131/10000 : ℝ)=(2500158150680813/2500000000000000 : ℝ) by norm_num, show 1+2*(12988473940557813/100000000000000000000 : ℝ)=(50012988473940557813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8349532619952501/25000000000000000000 : ℝ)+(12988473940557813/100000000000000000000 : ℝ) ≤ ((3123996754172061/3125000000000000 : ℝ)+(165646093649/97500000000000 : ℝ)*((2847/20000 : ℝ)+(1131/10000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (3123996754172061/3125000000000000 : ℝ)+(165646093649/97500000000000 : ℝ)*((2847/20000 : ℝ)+(1131/10000 : ℝ))=(10001129541004199/10000000000000000 : ℝ) by norm_num, show 1+(8349532619952501/25000000000000000000 : ℝ)+(12988473940557813/100000000000000000000 : ℝ)=(100046386604420367817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8349532619952501/25000000000000000000 : ℝ) ≤ ((3123996754172061/3125000000000000 : ℝ)+2*(165646093649/97500000000000 : ℝ)*(2847/20000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (3123996754172061/3125000000000000 : ℝ)+2*(165646093649/97500000000000 : ℝ)*(2847/20000 : ℝ)=(5000813239642573/5000000000000000 : ℝ) by norm_num, show 1+2*(8349532619952501/25000000000000000000 : ℝ)=(12508349532619952501/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3123996754172061/3125000000000000 : ℝ)*(X 1 0+X 2 0)+(165646093649/97500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3123996754172061/3125000000000000 : ℝ)) (alpha := (165646093649/97500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3123996754172061/3125000000000000 : ℝ)*(X 0 1+X 2 1)+(165646093649/97500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3123996754172061/3125000000000000 : ℝ)) (alpha := (165646093649/97500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3123996754172061/3125000000000000 : ℝ)*(X 0 2+X 1 2)+(165646093649/97500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (1131/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (3123996754172061/3125000000000000 : ℝ)) (alpha := (165646093649/97500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131412621/10000000000 : ℝ)*X 0 0+(2696507123/5000000000 : ℝ)*X 0 1+(2632797389/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336194401/2500000000 : ℝ)*X 1 0+(-1098021227/5000000000 : ℝ)*X 1 1+(658199347/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068955521/2000000000 : ℝ)*X 2 0+(1316398693/2500000000 : ℝ)*X 2 1+(-2196042459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354146107/10000000000 : ℝ)*X 0 0+(845477493/2000000000 : ℝ)*X 0 1+(4484619693/10000000000 : ℝ)*X 0 2+(4354146107/10000000000 : ℝ)*X 1 0+(845477493/2000000000 : ℝ)*X 1 1+(4484619693/10000000000 : ℝ)*X 1 2+(4354146107/10000000000 : ℝ)*X 2 0+(845477493/2000000000 : ℝ)*X 2 1+(4484619693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532854423/2500000000 : ℝ)*X 0 0+(2632961297/5000000000 : ℝ)*X 0 1+(215707407/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212492879/400000000 : ℝ)*X 1 0+(-1034475931/5000000000 : ℝ)*X 1 1+(1078537037/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328080453/2500000000 : ℝ)*X 2 0+(5392685373/10000000000 : ℝ)*X 2 1+(-2068951827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177078229/5000000000 : ℝ)*X 0 0+(2241978953/5000000000 : ℝ)*X 0 1+(2114025737/5000000000 : ℝ)*X 0 2+(2177078229/5000000000 : ℝ)*X 1 0+(2241978953/5000000000 : ℝ)*X 1 1+(2114025737/5000000000 : ℝ)*X 1 2+(2177078229/5000000000 : ℝ)*X 2 0+(2241978953/5000000000 : ℝ)*X 2 1+(2114025737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (789212755005505460176799/253906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (601837503/100000000000000 : ℝ)*(base19) + (559332133/100000000000000 : ℝ)*(base23) + (5875747/25000000000000 : ℝ)*(lower2) + (16526379/20000000000000 : ℝ)*(upper3) + (8629627/20000000000000 : ℝ)*(upper5) + (1466960168677231/25000000000000 : ℝ)*(major0) + (1466960168677231/25000000000000 : ℝ)*(major1) + (1466960168677231/25000000000000 : ℝ)*(major2) + (7848111281999633/100000000000000 : ℝ)*(sp0) + (1962031618661831/25000000000000 : ℝ)*(sp1) + (3924063258576347/50000000000000 : ℝ)*(sp2) + (194377271673989/5000000000000 : ℝ)*(sp3) + (3158897039/20000000000000 : ℝ)*(sp4) + (4367921879/50000000000000 : ℝ)*(sp7) + (1943777084661769/50000000000000 : ℝ)*(f.failure) + (1962031769121207/25000000000000 : ℝ)*(f.sum) + (25636415517551/4875000000000000000000000000 : ℝ)*base65 + (48488097108233201/3046875000000000000000000000000 : ℝ)*base68 + (14473530037124413/1523437500000000000000000000000 : ℝ)*base70 + (48764026142295701/3046875000000000000000000000000 : ℝ)*base72 + (7496891829331/1218750000000000000000000000 : ℝ)*base74 + (74469136181670701/3046875000000000000000000000000 : ℝ)*base76 + (37011882453701951/3046875000000000000000000000000 : ℝ)*base78 + (10111388783954299/3046875000000000000000000000000 : ℝ)*base79 + (1204971314713/2437500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31783/2441406250000000000 : ℝ)*base89 + (31783/2441406250000000000 : ℝ)*base91 + (31783/2441406250000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14466620352994947619018401/2031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1961682717/100000000000000 : ℝ)*(base19) + (490609957/25000000000000 : ℝ)*(base23) + (264140893/100000000000000 : ℝ)*(upper3) + (96476847/100000000000000 : ℝ)*(lower4) + (80124437/50000000000000 : ℝ)*(upper5) + (5898216054542181/100000000000000 : ℝ)*(major0) + (5898216054542181/100000000000000 : ℝ)*(major1) + (5898216054542181/100000000000000 : ℝ)*(major2) + (2038098231/4000000000000 : ℝ)*(sp1) + (3048475857/5000000000000 : ℝ)*(sp2) + (986094180654163/12500000000000 : ℝ)*(sp4) + (7888700531094811/100000000000000 : ℝ)*(sp5) + (493043157079771/6250000000000 : ℝ)*(sp6) + (3907678426450103/100000000000000 : ℝ)*(sp7) + (3907678426450103/100000000000000 : ℝ)*(f.failure) + (986094180654163/12500000000000 : ℝ)*(f.sum) + (5380627406927/1625000000000000000000000000 : ℝ)*base66 + (1415215647680717/4062500000000000000000000000000 : ℝ)*base68 + (45380985394819283/4062500000000000000000000000000 : ℝ)*base69 + (674066738256783/4062500000000000000000000000000 : ℝ)*base71 + (294029275573/1625000000000000000000000000 : ℝ)*base73 + (47720830065131783/4062500000000000000000000000000 : ℝ)*base75 + (30949215428569283/4062500000000000000000000000000 : ℝ)*base77 + (26065469652680717/4062500000000000000000000000000 : ℝ)*base80 + (3546654781573/1625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (23707/39062500000000000000 : ℝ)*base90 + (23707/39062500000000000000 : ℝ)*base92 + (23707/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1217_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1131/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1217_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1217_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1217_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1217_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
