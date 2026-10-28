-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:46.217261+00:00
-- url     : https://prove2.me/submissions/3a98e422-acc5-4499-a1e6-1eedc14593cd

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
theorem support_rectangle_w1218_s3_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-133000801/625000000 : ℝ)*x 0 + (2710904829/5000000000 : ℝ)*x 1 + (5238718479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133000801/625000000 : ℝ)^8411 ≤ (6466146248533/50000000000000 : ℝ)^6363 := by
    have hnat : (133000801 : ℕ)^8411*50000000000000^6363 ≤ 6466146248533^6363*625000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133000801 625000000 6466146248533 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710904829/5000000000 : ℝ)^8411 ≤ (44522110090431/100000000000000 : ℝ)^6363 := by
    have hnat : (2710904829 : ℕ)^8411*100000000000000^6363 ≤ 44522110090431^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710904829 5000000000 44522110090431 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238718479/10000000000 : ℝ)^8411 ≤ (42545597394931/100000000000000 : ℝ)^6363 := by
    have hnat : (5238718479 : ℕ)^8411*100000000000000^6363 ≤ 42545597394931^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238718479 10000000000 42545597394931 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133000801/625000000 : ℝ), (2710904829/5000000000 : ℝ), (5238718479/10000000000 : ℝ)] ![(6466146248533/50000000000000 : ℝ), (44522110090431/100000000000000 : ℝ), (42545597394931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133000801/625000000 : ℝ)|^8411 ≤ (6466146248533/50000000000000 : ℝ)^6363
        have hw : |(-133000801/625000000 : ℝ)|=(133000801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710904829/5000000000 : ℝ)|^8411 ≤ (44522110090431/100000000000000 : ℝ)^6363
        have hw : |(2710904829/5000000000 : ℝ)|=(2710904829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238718479/10000000000 : ℝ)|^8411 ≤ (42545597394931/100000000000000 : ℝ)^6363
        have hw : |(5238718479/10000000000 : ℝ)|=(5238718479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352026221/10000000000 : ℝ)*x 0 + (-2221456967/10000000000 : ℝ)*x 1 + (5238718281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352026221/10000000000 : ℝ)^8411 ≤ (43766206501503/100000000000000 : ℝ)^6363 := by
    have hnat : (5352026221 : ℕ)^8411*100000000000000^6363 ≤ 43766206501503^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352026221 10000000000 43766206501503 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2221456967/10000000000 : ℝ)^8411 ≤ (1711024778151/12500000000000 : ℝ)^6363 := by
    have hnat : (2221456967 : ℕ)^8411*12500000000000^6363 ≤ 1711024778151^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221456967 10000000000 1711024778151 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238718281/10000000000 : ℝ)^8411 ≤ (5318199408667/12500000000000 : ℝ)^6363 := by
    have hnat : (5238718281 : ℕ)^8411*12500000000000^6363 ≤ 5318199408667^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238718281 10000000000 5318199408667 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352026221/10000000000 : ℝ), (-2221456967/10000000000 : ℝ), (5238718281/10000000000 : ℝ)] ![(43766206501503/100000000000000 : ℝ), (1711024778151/12500000000000 : ℝ), (5318199408667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352026221/10000000000 : ℝ)|^8411 ≤ (43766206501503/100000000000000 : ℝ)^6363
        have hw : |(5352026221/10000000000 : ℝ)|=(5352026221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2221456967/10000000000 : ℝ)|^8411 ≤ (1711024778151/12500000000000 : ℝ)^6363
        have hw : |(-2221456967/10000000000 : ℝ)|=(2221456967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238718281/10000000000 : ℝ)|^8411 ≤ (5318199408667/12500000000000 : ℝ)^6363
        have hw : |(5238718281/10000000000 : ℝ)|=(5238718281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352026317/10000000000 : ℝ)*x 0 + (5238718169/10000000000 : ℝ)*x 1 + (-1110728493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352026317/10000000000 : ℝ)^8411 ≤ (43766207539217/100000000000000 : ℝ)^6363 := by
    have hnat : (5352026317 : ℕ)^8411*100000000000000^6363 ≤ 43766207539217^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352026317 10000000000 43766207539217 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238718169/10000000000 : ℝ)^8411 ≤ (42545594066979/100000000000000 : ℝ)^6363 := by
    have hnat : (5238718169 : ℕ)^8411*100000000000000^6363 ≤ 42545594066979^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238718169 10000000000 42545594066979 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110728493/5000000000 : ℝ)^8411 ≤ (3422049594991/25000000000000 : ℝ)^6363 := by
    have hnat : (1110728493 : ℕ)^8411*25000000000000^6363 ≤ 3422049594991^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110728493 5000000000 3422049594991 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352026317/10000000000 : ℝ), (5238718169/10000000000 : ℝ), (-1110728493/5000000000 : ℝ)] ![(43766207539217/100000000000000 : ℝ), (42545594066979/100000000000000 : ℝ), (3422049594991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352026317/10000000000 : ℝ)|^8411 ≤ (43766207539217/100000000000000 : ℝ)^6363
        have hw : |(5352026317/10000000000 : ℝ)|=(5352026317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238718169/10000000000 : ℝ)|^8411 ≤ (42545594066979/100000000000000 : ℝ)^6363
        have hw : |(5238718169/10000000000 : ℝ)|=(5238718169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110728493/5000000000 : ℝ)|^8411 ≤ (3422049594991/25000000000000 : ℝ)^6363
        have hw : |(-1110728493/5000000000 : ℝ)|=(1110728493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87045123/200000000 : ℝ)*x 0 + (4171242659/10000000000 : ℝ)*x 1 + (4540935953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87045123/200000000 : ℝ)^8411 ≤ (33298970453703/100000000000000 : ℝ)^6363 := by
    have hnat : (87045123 : ℕ)^8411*100000000000000^6363 ≤ 33298970453703^6363*200000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87045123 200000000 33298970453703 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171242659/10000000000 : ℝ)^8411 ≤ (787016460633/2500000000000 : ℝ)^6363 := by
    have hnat : (4171242659 : ℕ)^8411*2500000000000^6363 ≤ 787016460633^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171242659 10000000000 787016460633 2500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540935953/10000000000 : ℝ)^8411 ≤ (35220371104681/100000000000000 : ℝ)^6363 := by
    have hnat : (4540935953 : ℕ)^8411*100000000000000^6363 ≤ 35220371104681^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540935953 10000000000 35220371104681 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87045123/200000000 : ℝ), (4171242659/10000000000 : ℝ), (4540935953/10000000000 : ℝ)] ![(33298970453703/100000000000000 : ℝ), (787016460633/2500000000000 : ℝ), (35220371104681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87045123/200000000 : ℝ)|^8411 ≤ (33298970453703/100000000000000 : ℝ)^6363
        have hw : |(87045123/200000000 : ℝ)|=(87045123/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171242659/10000000000 : ℝ)|^8411 ≤ (787016460633/2500000000000 : ℝ)^6363
        have hw : |(4171242659/10000000000 : ℝ)|=(4171242659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4540935953/10000000000 : ℝ)|^8411 ≤ (35220371104681/100000000000000 : ℝ)^6363
        have hw : |(4540935953/10000000000 : ℝ)|=(4540935953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266003451/1250000000 : ℝ)*x 0 + (2619696911/5000000000 : ℝ)*x 1 + (5421130767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266003451/1250000000 : ℝ)^8411 ≤ (6466205661929/50000000000000 : ℝ)^6363 := by
    have hnat : (266003451 : ℕ)^8411*50000000000000^6363 ≤ 6466205661929^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266003451 1250000000 6466205661929 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619696911/5000000000 : ℝ)^8411 ≤ (10638211893309/25000000000000 : ℝ)^6363 := by
    have hnat : (2619696911 : ℕ)^8411*25000000000000^6363 ≤ 10638211893309^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619696911 5000000000 10638211893309 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421130767/10000000000 : ℝ)^8411 ≤ (22257370545851/50000000000000 : ℝ)^6363 := by
    have hnat : (5421130767 : ℕ)^8411*50000000000000^6363 ≤ 22257370545851^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421130767 10000000000 22257370545851 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266003451/1250000000 : ℝ), (2619696911/5000000000 : ℝ), (5421130767/10000000000 : ℝ)] ![(6466205661929/50000000000000 : ℝ), (10638211893309/25000000000000 : ℝ), (22257370545851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266003451/1250000000 : ℝ)|^8411 ≤ (6466205661929/50000000000000 : ℝ)^6363
        have hw : |(-266003451/1250000000 : ℝ)|=(266003451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619696911/5000000000 : ℝ)|^8411 ≤ (10638211893309/25000000000000 : ℝ)^6363
        have hw : |(2619696911/5000000000 : ℝ)|=(2619696911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421130767/10000000000 : ℝ)|^8411 ≤ (22257370545851/50000000000000 : ℝ)^6363
        have hw : |(5421130767/10000000000 : ℝ)|=(5421130767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305390937/10000000000 : ℝ)*x 0 + (-1019522241/5000000000 : ℝ)*x 1 + (5421130723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305390937/10000000000 : ℝ)^8411 ≤ (21631404895533/50000000000000 : ℝ)^6363 := by
    have hnat : (5305390937 : ℕ)^8411*50000000000000^6363 ≤ 21631404895533^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305390937 10000000000 21631404895533 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019522241/5000000000 : ℝ)^8411 ≤ (12222449587023/100000000000000 : ℝ)^6363 := by
    have hnat : (1019522241 : ℕ)^8411*100000000000000^6363 ≤ 12222449587023^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019522241 5000000000 12222449587023 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421130723/10000000000 : ℝ)^8411 ≤ (8902948122823/20000000000000 : ℝ)^6363 := by
    have hnat : (5421130723 : ℕ)^8411*20000000000000^6363 ≤ 8902948122823^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421130723 10000000000 8902948122823 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305390937/10000000000 : ℝ), (-1019522241/5000000000 : ℝ), (5421130723/10000000000 : ℝ)] ![(21631404895533/50000000000000 : ℝ), (12222449587023/100000000000000 : ℝ), (8902948122823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305390937/10000000000 : ℝ)|^8411 ≤ (21631404895533/50000000000000 : ℝ)^6363
        have hw : |(5305390937/10000000000 : ℝ)|=(5305390937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1019522241/5000000000 : ℝ)|^8411 ≤ (12222449587023/100000000000000 : ℝ)^6363
        have hw : |(-1019522241/5000000000 : ℝ)|=(1019522241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421130723/10000000000 : ℝ)|^8411 ≤ (8902948122823/20000000000000 : ℝ)^6363
        have hw : |(5421130723/10000000000 : ℝ)|=(5421130723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652695439/5000000000 : ℝ)*x 0 + (677641349/1250000000 : ℝ)*x 1 + (-2039044467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652695439/5000000000 : ℝ)^8411 ≤ (43262809155099/100000000000000 : ℝ)^6363 := by
    have hnat : (2652695439 : ℕ)^8411*100000000000000^6363 ≤ 43262809155099^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652695439 5000000000 43262809155099 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677641349/1250000000 : ℝ)^8411 ≤ (22257370681529/50000000000000 : ℝ)^6363 := by
    have hnat : (677641349 : ℕ)^8411*50000000000000^6363 ≤ 22257370681529^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677641349 1250000000 22257370681529 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2039044467/10000000000 : ℝ)^8411 ≤ (1222244946817/10000000000000 : ℝ)^6363 := by
    have hnat : (2039044467 : ℕ)^8411*10000000000000^6363 ≤ 1222244946817^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039044467 10000000000 1222244946817 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652695439/5000000000 : ℝ), (677641349/1250000000 : ℝ), (-2039044467/10000000000 : ℝ)] ![(43262809155099/100000000000000 : ℝ), (22257370681529/50000000000000 : ℝ), (1222244946817/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652695439/5000000000 : ℝ)|^8411 ≤ (43262809155099/100000000000000 : ℝ)^6363
        have hw : |(2652695439/5000000000 : ℝ)|=(2652695439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677641349/1250000000 : ℝ)|^8411 ≤ (22257370681529/50000000000000 : ℝ)^6363
        have hw : |(677641349/1250000000 : ℝ)|=(677641349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2039044467/10000000000 : ℝ)|^8411 ≤ (1222244946817/10000000000000 : ℝ)^6363
        have hw : |(-2039044467/10000000000 : ℝ)|=(2039044467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s3_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43522861/100000000 : ℝ)*x 0 + (4539572123/10000000000 : ℝ)*x 1 + (4172613777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43522861/100000000 : ℝ)^8411 ≤ (16649636676887/50000000000000 : ℝ)^6363 := by
    have hnat : (43522861 : ℕ)^8411*50000000000000^6363 ≤ 16649636676887^6363*100000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43522861 100000000 16649636676887 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539572123/10000000000 : ℝ)^8411 ≤ (35206388969163/100000000000000 : ℝ)^6363 := by
    have hnat : (4539572123 : ℕ)^8411*100000000000000^6363 ≤ 35206388969163^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539572123 10000000000 35206388969163 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172613777/10000000000 : ℝ)^8411 ≤ (6298867532409/20000000000000 : ℝ)^6363 := by
    have hnat : (4172613777 : ℕ)^8411*20000000000000^6363 ≤ 6298867532409^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172613777 10000000000 6298867532409 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43522861/100000000 : ℝ), (4539572123/10000000000 : ℝ), (4172613777/10000000000 : ℝ)] ![(16649636676887/50000000000000 : ℝ), (35206388969163/100000000000000 : ℝ), (6298867532409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43522861/100000000 : ℝ)|^8411 ≤ (16649636676887/50000000000000 : ℝ)^6363
        have hw : |(43522861/100000000 : ℝ)|=(43522861/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539572123/10000000000 : ℝ)|^8411 ≤ (35206388969163/100000000000000 : ℝ)^6363
        have hw : |(4539572123/10000000000 : ℝ)|=(4539572123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172613777/10000000000 : ℝ)|^8411 ≤ (6298867532409/20000000000000 : ℝ)^6363
        have hw : |(4172613777/10000000000 : ℝ)|=(4172613777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    (339/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3681/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (47/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (47/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (47/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (47/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (47/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (47/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (47/500 : ℝ) ^ (4205/1024 : ℝ) ≤ (6070237563712721/100000000000000000000 : ℝ) := by
    have hpowers : (47/500 : ℝ)^4205 ≤ (6070237563712721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (47 : ℕ)^4205*100000000000000000000^1024 ≤ 6070237563712721^1024*500^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47 500 6070237563712721 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47/500 : ℝ)) (X := (6070237563712721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16287/100000 : ℝ) ^ (4205/1024 : ℝ) ≤ (14501354631636031/25000000000000000000 : ℝ) := by
    have hpowers : (16287/100000 : ℝ)^4205 ≤ (14501354631636031/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16287 : ℕ)^4205*25000000000000000000^1024 ≤ 14501354631636031^1024*100000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16287 100000 14501354631636031 25000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16287/100000 : ℝ)) (X := (14501354631636031/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006070237563712721/50000000000000000000 : ℝ) ≤ (1250036953851661/1250000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50006070237563712721/50000000000000000000 : ℝ)^1024 ≤ (1250036953851661/1250000000000000 : ℝ)^4205 := by
      have hnat : (50006070237563712721 : ℕ)^1024*1250000000000000^4205 ≤ 1250036953851661^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006070237563712721 50000000000000000000 1250036953851661 1250000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036953851661/1250000000000000 : ℝ)) (X := (50006070237563712721/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012815131218051369/20000000000000000000 : ℝ) ≤ (2000311997982051/2000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (20012815131218051369/20000000000000000000 : ℝ)^1024 ≤ (2000311997982051/2000000000000000 : ℝ)^4205 := by
      have hnat : (20012815131218051369 : ℕ)^1024*2000000000000000^4205 ≤ 2000311997982051^4205*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012815131218051369 20000000000000000000 2000311997982051 2000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000311997982051/2000000000000000 : ℝ)) (X := (20012815131218051369/20000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514501354631636031/12500000000000000000 : ℝ) ≤ (5001412174503611/5000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (12514501354631636031/12500000000000000000 : ℝ)^1024 ≤ (5001412174503611/5000000000000000 : ℝ)^4205 := by
      have hnat : (12514501354631636031 : ℕ)^1024*5000000000000000^4205 ≤ 5001412174503611^4205*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514501354631636031 12500000000000000000 5001412174503611 5000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001412174503611/5000000000000000 : ℝ)) (X := (12514501354631636031/12500000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6070237563712721/100000000000000000000 : ℝ) ≤ ((8606033257298516857/8608750000000000000 : ℝ)+2*(1264359096967/688700000000000 : ℝ)*(47/500 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (8606033257298516857/8608750000000000000 : ℝ)+2*(1264359096967/688700000000000 : ℝ)*(47/500 : ℝ)=(1250036953851661/1250000000000000 : ℝ) by norm_num, show 1+2*(6070237563712721/100000000000000000000 : ℝ)=(50006070237563712721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14501354631636031/25000000000000000000 : ℝ)+(6070237563712721/100000000000000000000 : ℝ) ≤ ((8606033257298516857/8608750000000000000 : ℝ)+(1264359096967/688700000000000 : ℝ)*((16287/100000 : ℝ)+(47/500 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (8606033257298516857/8608750000000000000 : ℝ)+(1264359096967/688700000000000 : ℝ)*((16287/100000 : ℝ)+(47/500 : ℝ))=(2000311997982051/2000000000000000 : ℝ) by norm_num, show 1+(14501354631636031/25000000000000000000 : ℝ)+(6070237563712721/100000000000000000000 : ℝ)=(20012815131218051369/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14501354631636031/25000000000000000000 : ℝ) ≤ ((8606033257298516857/8608750000000000000 : ℝ)+2*(1264359096967/688700000000000 : ℝ)*(16287/100000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (8606033257298516857/8608750000000000000 : ℝ)+2*(1264359096967/688700000000000 : ℝ)*(16287/100000 : ℝ)=(5001412174503611/5000000000000000 : ℝ) by norm_num, show 1+2*(14501354631636031/25000000000000000000 : ℝ)=(12514501354631636031/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8606033257298516857/8608750000000000000 : ℝ)*(X 1 0+X 2 0)+(1264359096967/688700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (47/500 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (8606033257298516857/8608750000000000000 : ℝ)) (alpha := (1264359096967/688700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8606033257298516857/8608750000000000000 : ℝ)*(X 0 1+X 2 1)+(1264359096967/688700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (47/500 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (8606033257298516857/8608750000000000000 : ℝ)) (alpha := (1264359096967/688700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8606033257298516857/8608750000000000000 : ℝ)*(X 0 2+X 1 2)+(1264359096967/688700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (47/500 : ℝ)) (hi := (16287/100000 : ℝ)) (c := (8606033257298516857/8608750000000000000 : ℝ)) (alpha := (1264359096967/688700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-133000801/625000000 : ℝ)*X 0 0+(2710904829/5000000000 : ℝ)*X 0 1+(5238718479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352026221/10000000000 : ℝ)*X 1 0+(-2221456967/10000000000 : ℝ)*X 1 1+(5238718281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352026317/10000000000 : ℝ)*X 2 0+(5238718169/10000000000 : ℝ)*X 2 1+(-1110728493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87045123/200000000 : ℝ)*X 0 0+(4171242659/10000000000 : ℝ)*X 0 1+(4540935953/10000000000 : ℝ)*X 0 2+(87045123/200000000 : ℝ)*X 1 0+(4171242659/10000000000 : ℝ)*X 1 1+(4540935953/10000000000 : ℝ)*X 1 2+(87045123/200000000 : ℝ)*X 2 0+(4171242659/10000000000 : ℝ)*X 2 1+(4540935953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-266003451/1250000000 : ℝ)*X 0 0+(2619696911/5000000000 : ℝ)*X 0 1+(5421130767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305390937/10000000000 : ℝ)*X 1 0+(-1019522241/5000000000 : ℝ)*X 1 1+(5421130723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652695439/5000000000 : ℝ)*X 2 0+(677641349/1250000000 : ℝ)*X 2 1+(-2039044467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43522861/100000000 : ℝ)*X 0 0+(4539572123/10000000000 : ℝ)*X 0 1+(4172613777/10000000000 : ℝ)*X 0 2+(43522861/100000000 : ℝ)*X 1 0+(4539572123/10000000000 : ℝ)*X 1 1+(4172613777/10000000000 : ℝ)*X 1 2+(43522861/100000000 : ℝ)*X 2 0+(4539572123/10000000000 : ℝ)*X 2 1+(4172613777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3882039440712996004401323541/430437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199615883/10000000000000 : ℝ)*(base19) + (1993685331/100000000000000 : ℝ)*(base23) + (53757329/100000000000000 : ℝ)*(lower2) + (250471621/100000000000000 : ℝ)*(upper3) + (42243567/25000000000000 : ℝ)*(upper5) + (4083402814026929/100000000000000 : ℝ)*(major0) + (4083402814026929/100000000000000 : ℝ)*(major1) + (4083402814026929/100000000000000 : ℝ)*(major2) + (2730896412214983/50000000000000 : ℝ)*(sp0) + (682727908987751/12500000000000 : ℝ)*(sp1) + (5461823274375507/100000000000000 : ℝ)*(sp2) + (42265022965173/1562500000000 : ℝ)*(sp3) + (4055453859/12500000000000 : ℝ)*(sp4) + (18589594521/100000000000000 : ℝ)*(sp7) + (2704980059365593/100000000000000 : ℝ)*(f.failure) + (2730912634030419/50000000000000 : ℝ)*(f.sum) + (104004504588763/34435000000000000000000000000 : ℝ)*base65 + (6133742976607604653/860875000000000000000000000000000 : ℝ)*base67 + (129092541871895347/860875000000000000000000000000000 : ℝ)*base70 + (3632539770848229653/860875000000000000000000000000000 : ℝ)*base71 + (82755869684259/17217500000000000000000000000 : ℝ)*base73 + (5006519503281854653/860875000000000000000000000000000 : ℝ)*base75 + (24426402095281104653/860875000000000000000000000000000 : ℝ)*base77 + (18522407678439520347/860875000000000000000000000000000 : ℝ)*base80 + (37718709467821/17217500000000000000000000000 : ℝ)*base82 + (22105879/10000000000000000000000 : ℝ)*base89 + (22105879/10000000000000000000000 : ℝ)*base91 + (22105879/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2370622078746353679551665659/215218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2146647729/100000000000000 : ℝ)*(base19) + (56916819/2500000000000 : ℝ)*(base23) + (104128297/50000000000000 : ℝ)*(upper3) + (4514101/5000000000000 : ℝ)*(lower4) + (62946063/25000000000000 : ℝ)*(upper5) + (2056890454903457/50000000000000 : ℝ)*(major0) + (2056890454903457/50000000000000 : ℝ)*(major1) + (2056890454903457/50000000000000 : ℝ)*(major2) + (8228106773/20000000000000 : ℝ)*(sp1) + (43534677221/100000000000000 : ℝ)*(sp2) + (5502457945295261/100000000000000 : ℝ)*(sp4) + (2751207329056833/50000000000000 : ℝ)*(sp5) + (17195037918579/312500000000 : ℝ)*(sp6) + (340637938394227/12500000000000 : ℝ)*(sp7) + (340637938394227/12500000000000 : ℝ)*(f.failure) + (5502457945295261/100000000000000 : ℝ)*(f.sum) + (79480249770059/17217500000000000000000000000 : ℝ)*base65 + (1157532764210437149/430437500000000000000000000000000 : ℝ)*base67 + (2627231774767749649/430437500000000000000000000000000 : ℝ)*base69 + (6115601187545499649/430437500000000000000000000000000 : ℝ)*base71 + (243161134016097/34435000000000000000000000000 : ℝ)*base74 + (5921175664501999649/430437500000000000000000000000000 : ℝ)*base75 + (4813587283856124649/430437500000000000000000000000000 : ℝ)*base77 + (897155711152374649/430437500000000000000000000000000 : ℝ)*base79 + (5561239897907/8608750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14392419/1250000000000000000000 : ℝ)*base90 + (14392419/1250000000000000000000 : ℝ)*base92 + (14392419/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1218_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1218_s4_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66576797/312500000 : ℝ)*x 0 + (5398490017/10000000000 : ℝ)*x 1 + (5260436897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66576797/312500000 : ℝ)^8411 ≤ (6475967361307/50000000000000 : ℝ)^6363 := by
    have hnat : (66576797 : ℕ)^8411*50000000000000^6363 ≤ 6475967361307^6363*312500000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66576797 312500000 6475967361307 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398490017/10000000000 : ℝ)^8411 ≤ (885383162739/2000000000000 : ℝ)^6363 := by
    have hnat : (5398490017 : ℕ)^8411*2000000000000^6363 ≤ 885383162739^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398490017 10000000000 885383162739 2000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260436897/10000000000 : ℝ)^8411 ≤ (2673681695151/6250000000000 : ℝ)^6363 := by
    have hnat : (5260436897 : ℕ)^8411*6250000000000^6363 ≤ 2673681695151^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260436897 10000000000 2673681695151 6250000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66576797/312500000 : ℝ), (5398490017/10000000000 : ℝ), (5260436897/10000000000 : ℝ)] ![(6475967361307/50000000000000 : ℝ), (885383162739/2000000000000 : ℝ), (2673681695151/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66576797/312500000 : ℝ)|^8411 ≤ (6475967361307/50000000000000 : ℝ)^6363
        have hw : |(-66576797/312500000 : ℝ)|=(66576797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398490017/10000000000 : ℝ)|^8411 ≤ (885383162739/2000000000000 : ℝ)^6363
        have hw : |(5398490017/10000000000 : ℝ)|=(5398490017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260436897/10000000000 : ℝ)|^8411 ≤ (2673681695151/6250000000000 : ℝ)^6363
        have hw : |(5260436897/10000000000 : ℝ)|=(5260436897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20883439/39062500 : ℝ)*x 0 + (-1100281989/5000000000 : ℝ)*x 1 + (5260436923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20883439/39062500 : ℝ)^8411 ≤ (21851405404783/50000000000000 : ℝ)^6363 := by
    have hnat : (20883439 : ℕ)^8411*50000000000000^6363 ≤ 21851405404783^6363*39062500^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20883439 39062500 21851405404783 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100281989/5000000000 : ℝ)^8411 ≤ (2703656354649/20000000000000 : ℝ)^6363 := by
    have hnat : (1100281989 : ℕ)^8411*20000000000000^6363 ≤ 2703656354649^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100281989 5000000000 2703656354649 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260436923/10000000000 : ℝ)^8411 ≤ (21389453700953/50000000000000 : ℝ)^6363 := by
    have hnat : (5260436923 : ℕ)^8411*50000000000000^6363 ≤ 21389453700953^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260436923 10000000000 21389453700953 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20883439/39062500 : ℝ), (-1100281989/5000000000 : ℝ), (5260436923/10000000000 : ℝ)] ![(21851405404783/50000000000000 : ℝ), (2703656354649/20000000000000 : ℝ), (21389453700953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20883439/39062500 : ℝ)|^8411 ≤ (21851405404783/50000000000000 : ℝ)^6363
        have hw : |(20883439/39062500 : ℝ)|=(20883439/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100281989/5000000000 : ℝ)|^8411 ≤ (2703656354649/20000000000000 : ℝ)^6363
        have hw : |(-1100281989/5000000000 : ℝ)|=(1100281989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260436923/10000000000 : ℝ)|^8411 ≤ (21389453700953/50000000000000 : ℝ)^6363
        have hw : |(5260436923/10000000000 : ℝ)|=(5260436923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346160397/10000000000 : ℝ)*x 0 + (131510923/250000000 : ℝ)*x 1 + (-1100281983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346160397/10000000000 : ℝ)^8411 ≤ (43702810950041/100000000000000 : ℝ)^6363 := by
    have hnat : (5346160397 : ℕ)^8411*100000000000000^6363 ≤ 43702810950041^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346160397 10000000000 43702810950041 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131510923/250000000 : ℝ)^8411 ≤ (42778907369657/100000000000000 : ℝ)^6363 := by
    have hnat : (131510923 : ℕ)^8411*100000000000000^6363 ≤ 42778907369657^6363*250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131510923 250000000 42778907369657 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100281983/5000000000 : ℝ)^8411 ≤ (13518281675801/100000000000000 : ℝ)^6363 := by
    have hnat : (1100281983 : ℕ)^8411*100000000000000^6363 ≤ 13518281675801^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100281983 5000000000 13518281675801 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346160397/10000000000 : ℝ), (131510923/250000000 : ℝ), (-1100281983/5000000000 : ℝ)] ![(43702810950041/100000000000000 : ℝ), (42778907369657/100000000000000 : ℝ), (13518281675801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346160397/10000000000 : ℝ)|^8411 ≤ (43702810950041/100000000000000 : ℝ)^6363
        have hw : |(5346160397/10000000000 : ℝ)|=(5346160397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131510923/250000000 : ℝ)|^8411 ≤ (42778907369657/100000000000000 : ℝ)^6363
        have hw : |(131510923/250000000 : ℝ)|=(131510923/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1100281983/5000000000 : ℝ)|^8411 ≤ (13518281675801/100000000000000 : ℝ)^6363
        have hw : |(-1100281983/5000000000 : ℝ)|=(1100281983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10884303/25000000 : ℝ)*x 0 + (210826253/500000000 : ℝ)*x 1 + (4495278367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10884303/25000000 : ℝ)^8411 ≤ (33313788059583/100000000000000 : ℝ)^6363 := by
    have hnat : (10884303 : ℕ)^8411*100000000000000^6363 ≤ 33313788059583^6363*25000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10884303 25000000 33313788059583 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210826253/500000000 : ℝ)^8411 ≤ (31933190872389/100000000000000 : ℝ)^6363 := by
    have hnat : (210826253 : ℕ)^8411*100000000000000^6363 ≤ 31933190872389^6363*500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210826253 500000000 31933190872389 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495278367/10000000000 : ℝ)^8411 ≤ (8688255262267/25000000000000 : ℝ)^6363 := by
    have hnat : (4495278367 : ℕ)^8411*25000000000000^6363 ≤ 8688255262267^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495278367 10000000000 8688255262267 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10884303/25000000 : ℝ), (210826253/500000000 : ℝ), (4495278367/10000000000 : ℝ)] ![(33313788059583/100000000000000 : ℝ), (31933190872389/100000000000000 : ℝ), (8688255262267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10884303/25000000 : ℝ)|^8411 ≤ (33313788059583/100000000000000 : ℝ)^6363
        have hw : |(10884303/25000000 : ℝ)|=(10884303/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210826253/500000000 : ℝ)|^8411 ≤ (31933190872389/100000000000000 : ℝ)^6363
        have hw : |(210826253/500000000 : ℝ)|=(210826253/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495278367/10000000000 : ℝ)|^8411 ≤ (8688255262267/25000000000000 : ℝ)^6363
        have hw : |(4495278367/10000000000 : ℝ)|=(4495278367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130463431/10000000000 : ℝ)*x 0 + (5260821847/10000000000 : ℝ)*x 1 + (5398103861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130463431/10000000000 : ℝ)^8411 ≤ (2590396470567/20000000000000 : ℝ)^6363 := by
    have hnat : (2130463431 : ℕ)^8411*20000000000000^6363 ≤ 2590396470567^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130463431 10000000000 2590396470567 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260821847/10000000000 : ℝ)^8411 ≤ (42783045241823/100000000000000 : ℝ)^6363 := by
    have hnat : (5260821847 : ℕ)^8411*100000000000000^6363 ≤ 42783045241823^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260821847 10000000000 42783045241823 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398103861/10000000000 : ℝ)^8411 ≤ (4426497239493/10000000000000 : ℝ)^6363 := by
    have hnat : (5398103861 : ℕ)^8411*10000000000000^6363 ≤ 4426497239493^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398103861 10000000000 4426497239493 10000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130463431/10000000000 : ℝ), (5260821847/10000000000 : ℝ), (5398103861/10000000000 : ℝ)] ![(2590396470567/20000000000000 : ℝ), (42783045241823/100000000000000 : ℝ), (4426497239493/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130463431/10000000000 : ℝ)|^8411 ≤ (2590396470567/20000000000000 : ℝ)^6363
        have hw : |(-2130463431/10000000000 : ℝ)|=(2130463431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260821847/10000000000 : ℝ)|^8411 ≤ (42783045241823/100000000000000 : ℝ)^6363
        have hw : |(5260821847/10000000000 : ℝ)|=(5260821847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398103861/10000000000 : ℝ)|^8411 ≤ (4426497239493/10000000000000 : ℝ)^6363
        have hw : |(5398103861/10000000000 : ℝ)|=(5398103861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310995583/10000000000 : ℝ)*x 0 + (-2062896997/10000000000 : ℝ)*x 1 + (674762919/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310995583/10000000000 : ℝ)^8411 ≤ (2707702073381/6250000000000 : ℝ)^6363 := by
    have hnat : (5310995583 : ℕ)^8411*6250000000000^6363 ≤ 2707702073381^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310995583 10000000000 2707702073381 6250000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062896997/10000000000 : ℝ)^8411 ≤ (2482359986793/20000000000000 : ℝ)^6363 := by
    have hnat : (2062896997 : ℕ)^8411*20000000000000^6363 ≤ 2482359986793^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062896997 10000000000 2482359986793 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674762919/1250000000 : ℝ)^8411 ≤ (22132483438841/50000000000000 : ℝ)^6363 := by
    have hnat : (674762919 : ℕ)^8411*50000000000000^6363 ≤ 22132483438841^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674762919 1250000000 22132483438841 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310995583/10000000000 : ℝ), (-2062896997/10000000000 : ℝ), (674762919/1250000000 : ℝ)] ![(2707702073381/6250000000000 : ℝ), (2482359986793/20000000000000 : ℝ), (22132483438841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310995583/10000000000 : ℝ)|^8411 ≤ (2707702073381/6250000000000 : ℝ)^6363
        have hw : |(5310995583/10000000000 : ℝ)|=(5310995583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062896997/10000000000 : ℝ)|^8411 ≤ (2482359986793/20000000000000 : ℝ)^6363
        have hw : |(-2062896997/10000000000 : ℝ)|=(2062896997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674762919/1250000000 : ℝ)|^8411 ≤ (22132483438841/50000000000000 : ℝ)^6363
        have hw : |(674762919/1250000000 : ℝ)|=(674762919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310995143/10000000000 : ℝ)*x 0 + (215924153/400000000 : ℝ)*x 1 + (-515724237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310995143/10000000000 : ℝ)^8411 ≤ (21661614214837/50000000000000 : ℝ)^6363 := by
    have hnat : (5310995143 : ℕ)^8411*50000000000000^6363 ≤ 21661614214837^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310995143 10000000000 21661614214837 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215924153/400000000 : ℝ)^8411 ≤ (5533121500589/12500000000000 : ℝ)^6363 := by
    have hnat : (215924153 : ℕ)^8411*12500000000000^6363 ≤ 5533121500589^6363*400000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215924153 400000000 5533121500589 12500000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515724237/2500000000 : ℝ)^8411 ≤ (6205899772129/50000000000000 : ℝ)^6363 := by
    have hnat : (515724237 : ℕ)^8411*50000000000000^6363 ≤ 6205899772129^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515724237 2500000000 6205899772129 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310995143/10000000000 : ℝ), (215924153/400000000 : ℝ), (-515724237/2500000000 : ℝ)] ![(21661614214837/50000000000000 : ℝ), (5533121500589/12500000000000 : ℝ), (6205899772129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310995143/10000000000 : ℝ)|^8411 ≤ (21661614214837/50000000000000 : ℝ)^6363
        have hw : |(5310995143/10000000000 : ℝ)|=(5310995143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215924153/400000000 : ℝ)|^8411 ≤ (5533121500589/12500000000000 : ℝ)^6363
        have hw : |(215924153/400000000 : ℝ)|=(215924153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515724237/2500000000 : ℝ)|^8411 ≤ (6205899772129/50000000000000 : ℝ)^6363
        have hw : |(-515724237/2500000000 : ℝ)|=(515724237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s4_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353734299/10000000000 : ℝ)*x 0 + (4494501459/10000000000 : ℝ)*x 1 + (2108652431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353734299/10000000000 : ℝ)^8411 ≤ (6662784110183/20000000000000 : ℝ)^6363 := by
    have hnat : (4353734299 : ℕ)^8411*20000000000000^6363 ≤ 6662784110183^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353734299 10000000000 6662784110183 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494501459/10000000000 : ℝ)^8411 ≤ (34745081804207/100000000000000 : ℝ)^6363 := by
    have hnat : (4494501459 : ℕ)^8411*100000000000000^6363 ≤ 34745081804207^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494501459 10000000000 34745081804207 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108652431/5000000000 : ℝ)^8411 ≤ (31940997628473/100000000000000 : ℝ)^6363 := by
    have hnat : (2108652431 : ℕ)^8411*100000000000000^6363 ≤ 31940997628473^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108652431 5000000000 31940997628473 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353734299/10000000000 : ℝ), (4494501459/10000000000 : ℝ), (2108652431/5000000000 : ℝ)] ![(6662784110183/20000000000000 : ℝ), (34745081804207/100000000000000 : ℝ), (31940997628473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353734299/10000000000 : ℝ)|^8411 ≤ (6662784110183/20000000000000 : ℝ)^6363
        have hw : |(4353734299/10000000000 : ℝ)|=(4353734299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494501459/10000000000 : ℝ)|^8411 ≤ (34745081804207/100000000000000 : ℝ)^6363
        have hw : |(4494501459/10000000000 : ℝ)|=(4494501459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108652431/5000000000 : ℝ)|^8411 ≤ (31940997628473/100000000000000 : ℝ)^6363
        have hw : |(2108652431/5000000000 : ℝ)|=(2108652431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (707/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (339/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (339/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (339/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3681/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (339/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (339/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3681/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (339/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (339/3125 : ℝ) ^ (4205/1024 : ℝ) ≤ (10932417305442419/100000000000000000000 : ℝ) := by
    have hpowers : (339/3125 : ℝ)^4205 ≤ (10932417305442419/100000000000000000000 : ℝ)^1024 := by
      have hnat : (339 : ℕ)^4205*100000000000000000000^1024 ≤ 10932417305442419^1024*3125^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        339 3125 10932417305442419 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (339/3125 : ℝ)) (X := (10932417305442419/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3681/25000 : ℝ) ^ (4205/1024 : ℝ) ≤ (38330411555602233/100000000000000000000 : ℝ) := by
    have hpowers : (3681/25000 : ℝ)^4205 ≤ (38330411555602233/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3681 : ℕ)^4205*100000000000000000000^1024 ≤ 38330411555602233^1024*25000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3681 25000 38330411555602233 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3681/25000 : ℝ)) (X := (38330411555602233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010932417305442419/50000000000000000000 : ℝ) ≤ (10000532407591529/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50010932417305442419/50000000000000000000 : ℝ)^1024 ≤ (10000532407591529/10000000000000000 : ℝ)^4205 := by
      have hnat : (50010932417305442419 : ℕ)^1024*10000000000000000^4205 ≤ 10000532407591529^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010932417305442419 50000000000000000000 10000532407591529 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000532407591529/10000000000000000 : ℝ)) (X := (50010932417305442419/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012315707215261163/25000000000000000000 : ℝ) ≤ (10001199423066109/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (25012315707215261163/25000000000000000000 : ℝ)^1024 ≤ (10001199423066109/10000000000000000 : ℝ)^4205 := by
      have hnat : (25012315707215261163 : ℕ)^1024*10000000000000000^4205 ≤ 10001199423066109^4205*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012315707215261163 25000000000000000000 10001199423066109 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001199423066109/10000000000000000 : ℝ)) (X := (25012315707215261163/25000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038330411555602233/50000000000000000000 : ℝ) ≤ (10001866438540689/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50038330411555602233/50000000000000000000 : ℝ)^1024 ≤ (10001866438540689/10000000000000000 : ℝ)^4205 := by
      have hnat : (50038330411555602233 : ℕ)^1024*10000000000000000^4205 ≤ 10001866438540689^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038330411555602233 50000000000000000000 10001866438540689 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001866438540689/10000000000000000 : ℝ)) (X := (50038330411555602233/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10932417305442419/100000000000000000000 : ℝ) ≤ ((3228966003674023227/3230000000000000000 : ℝ)+2*(33350773729/19380000000000 : ℝ)*(339/3125 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (3228966003674023227/3230000000000000000 : ℝ)+2*(33350773729/19380000000000 : ℝ)*(339/3125 : ℝ)=(10000532407591529/10000000000000000 : ℝ) by norm_num, show 1+2*(10932417305442419/100000000000000000000 : ℝ)=(50010932417305442419/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38330411555602233/100000000000000000000 : ℝ)+(10932417305442419/100000000000000000000 : ℝ) ≤ ((3228966003674023227/3230000000000000000 : ℝ)+(33350773729/19380000000000 : ℝ)*((3681/25000 : ℝ)+(339/3125 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (3228966003674023227/3230000000000000000 : ℝ)+(33350773729/19380000000000 : ℝ)*((3681/25000 : ℝ)+(339/3125 : ℝ))=(10001199423066109/10000000000000000 : ℝ) by norm_num, show 1+(38330411555602233/100000000000000000000 : ℝ)+(10932417305442419/100000000000000000000 : ℝ)=(25012315707215261163/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38330411555602233/100000000000000000000 : ℝ) ≤ ((3228966003674023227/3230000000000000000 : ℝ)+2*(33350773729/19380000000000 : ℝ)*(3681/25000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (3228966003674023227/3230000000000000000 : ℝ)+2*(33350773729/19380000000000 : ℝ)*(3681/25000 : ℝ)=(10001866438540689/10000000000000000 : ℝ) by norm_num, show 1+2*(38330411555602233/100000000000000000000 : ℝ)=(50038330411555602233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3228966003674023227/3230000000000000000 : ℝ)*(X 1 0+X 2 0)+(33350773729/19380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (3228966003674023227/3230000000000000000 : ℝ)) (alpha := (33350773729/19380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3228966003674023227/3230000000000000000 : ℝ)*(X 0 1+X 2 1)+(33350773729/19380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (3228966003674023227/3230000000000000000 : ℝ)) (alpha := (33350773729/19380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3228966003674023227/3230000000000000000 : ℝ)*(X 0 2+X 1 2)+(33350773729/19380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (339/3125 : ℝ)) (hi := (3681/25000 : ℝ)) (c := (3228966003674023227/3230000000000000000 : ℝ)) (alpha := (33350773729/19380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66576797/312500000 : ℝ)*X 0 0+(5398490017/10000000000 : ℝ)*X 0 1+(5260436897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20883439/39062500 : ℝ)*X 1 0+(-1100281989/5000000000 : ℝ)*X 1 1+(5260436923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346160397/10000000000 : ℝ)*X 2 0+(131510923/250000000 : ℝ)*X 2 1+(-1100281983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((10884303/25000000 : ℝ)*X 0 0+(210826253/500000000 : ℝ)*X 0 1+(4495278367/10000000000 : ℝ)*X 0 2+(10884303/25000000 : ℝ)*X 1 0+(210826253/500000000 : ℝ)*X 1 1+(4495278367/10000000000 : ℝ)*X 1 2+(10884303/25000000 : ℝ)*X 2 0+(210826253/500000000 : ℝ)*X 2 1+(4495278367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130463431/10000000000 : ℝ)*X 0 0+(5260821847/10000000000 : ℝ)*X 0 1+(5398103861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310995583/10000000000 : ℝ)*X 1 0+(-2062896997/10000000000 : ℝ)*X 1 1+(674762919/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310995143/10000000000 : ℝ)*X 2 0+(215924153/400000000 : ℝ)*X 2 1+(-515724237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353734299/10000000000 : ℝ)*X 0 0+(4494501459/10000000000 : ℝ)*X 0 1+(2108652431/5000000000 : ℝ)*X 0 2+(4353734299/10000000000 : ℝ)*X 1 0+(4494501459/10000000000 : ℝ)*X 1 1+(2108652431/5000000000 : ℝ)*X 1 2+(4353734299/10000000000 : ℝ)*X 2 0+(4494501459/10000000000 : ℝ)*X 2 1+(2108652431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10735583755972696482265739/3230000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (631654039/100000000000000 : ℝ)*(base19) + (522222381/100000000000000 : ℝ)*(base23) + (6792063/10000000000000 : ℝ)*(lower2) + (86102509/100000000000000 : ℝ)*(upper3) + (3331859/25000000000000 : ℝ)*(upper5) + (216620855567819/4000000000000 : ℝ)*(major0) + (216620855567819/4000000000000 : ℝ)*(major1) + (216620855567819/4000000000000 : ℝ)*(major2) + (7243606677955633/100000000000000 : ℝ)*(sp0) + (7243622906361517/100000000000000 : ℝ)*(sp1) + (905452876974147/12500000000000 : ℝ)*(sp2) + (3587409200939153/100000000000000 : ℝ)*(sp3) + (4215014981/25000000000000 : ℝ)*(sp4) + (9928645893/100000000000000 : ℝ)*(sp7) + (1793709564792523/50000000000000 : ℝ)*(f.failure) + (7243623538015557/100000000000000 : ℝ)*(f.sum) + (253281652279/60562500000000000000000000 : ℝ)*base66 + (261249489629864261/38760000000000000000000000000000 : ℝ)*base68 + (425644190514375739/38760000000000000000000000000000 : ℝ)*base69 + (305070099067904261/38760000000000000000000000000000 : ℝ)*base72 + (2946786027973/484500000000000000000000000 : ℝ)*base73 + (148590435341384261/38760000000000000000000000000000 : ℝ)*base76 + (278190362481344261/38760000000000000000000000000000 : ℝ)*base78 + (551433304531424261/38760000000000000000000000000000 : ℝ)*base80 + (2274183040603/484500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13822331/5000000000000000000000 : ℝ)*base90 + (13822331/5000000000000000000000 : ℝ)*base92 + (13822331/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1690821913672781637440737761/161500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1950307161/100000000000000 : ℝ)*(base19) + (1259515839/50000000000000 : ℝ)*(base23) + (98990253/100000000000000 : ℝ)*(upper3) + (263526737/50000000000000 : ℝ)*(lower4) + (11365963/25000000000000 : ℝ)*(upper5) + (5445898399495227/100000000000000 : ℝ)*(major0) + (5445898399495227/100000000000000 : ℝ)*(major1) + (5445898399495227/100000000000000 : ℝ)*(major2) + (15535827737/50000000000000 : ℝ)*(sp1) + (58229585149/100000000000000 : ℝ)*(sp2) + (7284254591692059/100000000000000 : ℝ)*(sp4) + (455263848108089/6250000000000 : ℝ)*(sp5) + (227631057596101/3125000000000 : ℝ)*(sp6) + (1803770929157767/50000000000000 : ℝ)*(sp7) + (1803770929157767/50000000000000 : ℝ)*(f.failure) + (7284254591692059/100000000000000 : ℝ)*(f.sum) + (103825161739/32300000000000000000000000 : ℝ)*base66 + (2076645658862862471/323000000000000000000000000000000 : ℝ)*base68 + (2973903814906862471/323000000000000000000000000000000 : ℝ)*base70 + (1266949192647862471/323000000000000000000000000000000 : ℝ)*base72 + (1178628247177/323000000000000000000000000 : ℝ)*base74 + (8588017187079862471/323000000000000000000000000000000 : ℝ)*base76 + (1555732549730862471/323000000000000000000000000000000 : ℝ)*base78 + (10158638772623862471/323000000000000000000000000000000 : ℝ)*base80 + (578270616687/323000000000000000000000000 : ℝ)*base81 + (38696201/5000000000000000000000 : ℝ)*base89 + (38696201/5000000000000000000000 : ℝ)*base91 + (38696201/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1218_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3681/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (339/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1218_s5_0 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130944363/10000000000 : ℝ)*x 0 + (539299491/1000000000 : ℝ)*x 1 + (526561231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130944363/10000000000 : ℝ)^8411 ≤ (12955847333457/100000000000000 : ℝ)^6363 := by
    have hnat : (2130944363 : ℕ)^8411*100000000000000^6363 ≤ 12955847333457^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130944363 10000000000 12955847333457 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539299491/1000000000 : ℝ)^8411 ≤ (44209602940797/100000000000000 : ℝ)^6363 := by
    have hnat : (539299491 : ℕ)^8411*100000000000000^6363 ≤ 44209602940797^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539299491 1000000000 44209602940797 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526561231/1000000000 : ℝ)^8411 ≤ (535431871399/1250000000000 : ℝ)^6363 := by
    have hnat : (526561231 : ℕ)^8411*1250000000000^6363 ≤ 535431871399^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526561231 1000000000 535431871399 1250000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130944363/10000000000 : ℝ), (539299491/1000000000 : ℝ), (526561231/1000000000 : ℝ)] ![(12955847333457/100000000000000 : ℝ), (44209602940797/100000000000000 : ℝ), (535431871399/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130944363/10000000000 : ℝ)|^8411 ≤ (12955847333457/100000000000000 : ℝ)^6363
        have hw : |(-2130944363/10000000000 : ℝ)|=(2130944363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539299491/1000000000 : ℝ)|^8411 ≤ (44209602940797/100000000000000 : ℝ)^6363
        have hw : |(539299491/1000000000 : ℝ)|=(539299491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526561231/1000000000 : ℝ)|^8411 ≤ (535431871399/1250000000000 : ℝ)^6363
        have hw : |(526561231/1000000000 : ℝ)|=(526561231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_1 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344773603/10000000000 : ℝ)*x 0 + (-1097777613/5000000000 : ℝ)*x 1 + (1316403077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344773603/10000000000 : ℝ)^8411 ≤ (10921956572283/25000000000000 : ℝ)^6363 := by
    have hnat : (5344773603 : ℕ)^8411*25000000000000^6363 ≤ 10921956572283^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344773603 10000000000 10921956572283 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097777613/5000000000 : ℝ)^8411 ≤ (2695524800893/20000000000000 : ℝ)^6363 := by
    have hnat : (1097777613 : ℕ)^8411*20000000000000^6363 ≤ 2695524800893^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097777613 5000000000 2695524800893 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316403077/2500000000 : ℝ)^8411 ≤ (21417274845207/50000000000000 : ℝ)^6363 := by
    have hnat : (1316403077 : ℕ)^8411*50000000000000^6363 ≤ 21417274845207^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316403077 2500000000 21417274845207 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344773603/10000000000 : ℝ), (-1097777613/5000000000 : ℝ), (1316403077/2500000000 : ℝ)] ![(10921956572283/25000000000000 : ℝ), (2695524800893/20000000000000 : ℝ), (21417274845207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344773603/10000000000 : ℝ)|^8411 ≤ (10921956572283/25000000000000 : ℝ)^6363
        have hw : |(5344773603/10000000000 : ℝ)|=(5344773603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097777613/5000000000 : ℝ)|^8411 ≤ (2695524800893/20000000000000 : ℝ)^6363
        have hw : |(-1097777613/5000000000 : ℝ)|=(1097777613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316403077/2500000000 : ℝ)|^8411 ≤ (21417274845207/50000000000000 : ℝ)^6363
        have hw : |(1316403077/2500000000 : ℝ)|=(1316403077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_2 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336193401/2500000000 : ℝ)*x 0 + (329100769/625000000 : ℝ)*x 1 + (-219555523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336193401/2500000000 : ℝ)^8411 ≤ (43687826299937/100000000000000 : ℝ)^6363 := by
    have hnat : (1336193401 : ℕ)^8411*100000000000000^6363 ≤ 43687826299937^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336193401 2500000000 43687826299937 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329100769/625000000 : ℝ)^8411 ≤ (21417274823701/50000000000000 : ℝ)^6363 := by
    have hnat : (329100769 : ℕ)^8411*50000000000000^6363 ≤ 21417274823701^6363*625000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329100769 625000000 21417274823701 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219555523/1000000000 : ℝ)^8411 ≤ (6738812018461/50000000000000 : ℝ)^6363 := by
    have hnat : (219555523 : ℕ)^8411*50000000000000^6363 ≤ 6738812018461^6363*1000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219555523 1000000000 6738812018461 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336193401/2500000000 : ℝ), (329100769/625000000 : ℝ), (-219555523/1000000000 : ℝ)] ![(43687826299937/100000000000000 : ℝ), (21417274823701/50000000000000 : ℝ), (6738812018461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336193401/2500000000 : ℝ)|^8411 ≤ (43687826299937/100000000000000 : ℝ)^6363
        have hw : |(1336193401/2500000000 : ℝ)|=(1336193401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329100769/625000000 : ℝ)|^8411 ≤ (21417274823701/50000000000000 : ℝ)^6363
        have hw : |(329100769/625000000 : ℝ)|=(329100769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219555523/1000000000 : ℝ)|^8411 ≤ (6738812018461/50000000000000 : ℝ)^6363
        have hw : |(-219555523/1000000000 : ℝ)|=(219555523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_3 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177004087/5000000000 : ℝ)*x 0 + (4227261097/10000000000 : ℝ)*x 1 + (4484468747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177004087/5000000000 : ℝ)^8411 ≤ (16658345360137/50000000000000 : ℝ)^6363 := by
    have hnat : (2177004087 : ℕ)^8411*50000000000000^6363 ≤ 16658345360137^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177004087 5000000000 16658345360137 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227261097/10000000000 : ℝ)^8411 ≤ (6408142466693/20000000000000 : ℝ)^6363 := by
    have hnat : (4227261097 : ℕ)^8411*20000000000000^6363 ≤ 6408142466693^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227261097 10000000000 6408142466693 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484468747/10000000000 : ℝ)^8411 ≤ (8660649233893/25000000000000 : ℝ)^6363 := by
    have hnat : (4484468747 : ℕ)^8411*25000000000000^6363 ≤ 8660649233893^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484468747 10000000000 8660649233893 25000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177004087/5000000000 : ℝ), (4227261097/10000000000 : ℝ), (4484468747/10000000000 : ℝ)] ![(16658345360137/50000000000000 : ℝ), (6408142466693/20000000000000 : ℝ), (8660649233893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177004087/5000000000 : ℝ)|^8411 ≤ (16658345360137/50000000000000 : ℝ)^6363
        have hw : |(2177004087/5000000000 : ℝ)|=(2177004087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227261097/10000000000 : ℝ)|^8411 ≤ (6408142466693/20000000000000 : ℝ)^6363
        have hw : |(4227261097/10000000000 : ℝ)|=(4227261097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484468747/10000000000 : ℝ)|^8411 ≤ (8660649233893/25000000000000 : ℝ)^6363
        have hw : |(4484468747/10000000000 : ℝ)|=(4484468747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_4 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130949439/10000000000 : ℝ)*x 0 + (1316485007/2500000000 : ℝ)*x 1 + (1348166483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130949439/10000000000 : ℝ)^8411 ≤ (6477944063959/50000000000000 : ℝ)^6363 := by
    have hnat : (2130949439 : ℕ)^8411*50000000000000^6363 ≤ 6477944063959^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130949439 10000000000 6477944063959 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316485007/2500000000 : ℝ)^8411 ≤ (669344901721/1562500000000 : ℝ)^6363 := by
    have hnat : (1316485007 : ℕ)^8411*1562500000000^6363 ≤ 669344901721^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316485007 2500000000 669344901721 1562500000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348166483/2500000000 : ℝ)^8411 ≤ (8841207628591/20000000000000 : ℝ)^6363 := by
    have hnat : (1348166483 : ℕ)^8411*20000000000000^6363 ≤ 8841207628591^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348166483 2500000000 8841207628591 20000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130949439/10000000000 : ℝ), (1316485007/2500000000 : ℝ), (1348166483/2500000000 : ℝ)] ![(6477944063959/50000000000000 : ℝ), (669344901721/1562500000000 : ℝ), (8841207628591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130949439/10000000000 : ℝ)|^8411 ≤ (6477944063959/50000000000000 : ℝ)^6363
        have hw : |(-2130949439/10000000000 : ℝ)|=(2130949439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316485007/2500000000 : ℝ)|^8411 ≤ (669344901721/1562500000000 : ℝ)^6363
        have hw : |(1316485007/2500000000 : ℝ)|=(1316485007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348166483/2500000000 : ℝ)|^8411 ≤ (8841207628591/20000000000000 : ℝ)^6363
        have hw : |(1348166483/2500000000 : ℝ)|=(1348166483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_5 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656162523/5000000000 : ℝ)*x 0 + (-2068501399/10000000000 : ℝ)*x 1 + (5392665963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656162523/5000000000 : ℝ)^8411 ≤ (21668784527407/50000000000000 : ℝ)^6363 := by
    have hnat : (2656162523 : ℕ)^8411*50000000000000^6363 ≤ 21668784527407^6363*5000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656162523 5000000000 21668784527407 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068501399/10000000000 : ℝ)^8411 ≤ (12456392445351/100000000000000 : ℝ)^6363 := by
    have hnat : (2068501399 : ℕ)^8411*100000000000000^6363 ≤ 12456392445351^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068501399 10000000000 12456392445351 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392665963/10000000000 : ℝ)^8411 ≤ (44206038478867/100000000000000 : ℝ)^6363 := by
    have hnat : (5392665963 : ℕ)^8411*100000000000000^6363 ≤ 44206038478867^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392665963 10000000000 44206038478867 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656162523/5000000000 : ℝ), (-2068501399/10000000000 : ℝ), (5392665963/10000000000 : ℝ)] ![(21668784527407/50000000000000 : ℝ), (12456392445351/100000000000000 : ℝ), (44206038478867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656162523/5000000000 : ℝ)|^8411 ≤ (21668784527407/50000000000000 : ℝ)^6363
        have hw : |(2656162523/5000000000 : ℝ)|=(2656162523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068501399/10000000000 : ℝ)|^8411 ≤ (12456392445351/100000000000000 : ℝ)^6363
        have hw : |(-2068501399/10000000000 : ℝ)|=(2068501399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392665963/10000000000 : ℝ)|^8411 ≤ (44206038478867/100000000000000 : ℝ)^6363
        have hw : |(5392665963/10000000000 : ℝ)|=(5392665963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_6 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664040611/1250000000 : ℝ)*x 0 + (5392666129/10000000000 : ℝ)*x 1 + (-517125347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664040611/1250000000 : ℝ)^8411 ≤ (21668783675499/50000000000000 : ℝ)^6363 := by
    have hnat : (664040611 : ℕ)^8411*50000000000000^6363 ≤ 21668783675499^6363*1250000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664040611 1250000000 21668783675499 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392666129/10000000000 : ℝ)^8411 ≤ (22103020138811/50000000000000 : ℝ)^6363 := by
    have hnat : (5392666129 : ℕ)^8411*50000000000000^6363 ≤ 22103020138811^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392666129 10000000000 22103020138811 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517125347/2500000000 : ℝ)^8411 ≤ (12456392357789/100000000000000 : ℝ)^6363 := by
    have hnat : (517125347 : ℕ)^8411*100000000000000^6363 ≤ 12456392357789^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517125347 2500000000 12456392357789 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664040611/1250000000 : ℝ), (5392666129/10000000000 : ℝ), (-517125347/2500000000 : ℝ)] ![(21668783675499/50000000000000 : ℝ), (22103020138811/50000000000000 : ℝ), (12456392357789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664040611/1250000000 : ℝ)|^8411 ≤ (21668783675499/50000000000000 : ℝ)^6363
        have hw : |(664040611/1250000000 : ℝ)|=(664040611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392666129/10000000000 : ℝ)|^8411 ≤ (22103020138811/50000000000000 : ℝ)^6363
        have hw : |(5392666129/10000000000 : ℝ)|=(5392666129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517125347/2500000000 : ℝ)|^8411 ≤ (12456392357789/100000000000000 : ℝ)^6363
        have hw : |(-517125347/2500000000 : ℝ)|=(517125347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1218_s5_7 (p : ℝ) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088504629/2500000000 : ℝ)*x 0 + (4483807007/10000000000 : ℝ)*x 1 + (4227925063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088504629/2500000000 : ℝ)^8411 ≤ (33316795327823/100000000000000 : ℝ)^6363 := by
    have hnat : (1088504629 : ℕ)^8411*100000000000000^6363 ≤ 33316795327823^6363*2500000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088504629 2500000000 33316795327823 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483807007/10000000000 : ℝ)^8411 ≤ (34635839806383/100000000000000 : ℝ)^6363 := by
    have hnat : (4483807007 : ℕ)^8411*100000000000000^6363 ≤ 34635839806383^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483807007 10000000000 34635839806383 100000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227925063/10000000000 : ℝ)^8411 ≤ (16023682422357/50000000000000 : ℝ)^6363 := by
    have hnat : (4227925063 : ℕ)^8411*50000000000000^6363 ≤ 16023682422357^6363*10000000000^8411 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227925063 10000000000 16023682422357 50000000000000 8411 6363 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8411/2048 : ℝ)) 8411 6363 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088504629/2500000000 : ℝ), (4483807007/10000000000 : ℝ), (4227925063/10000000000 : ℝ)] ![(33316795327823/100000000000000 : ℝ), (34635839806383/100000000000000 : ℝ), (16023682422357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088504629/2500000000 : ℝ)|^8411 ≤ (33316795327823/100000000000000 : ℝ)^6363
        have hw : |(1088504629/2500000000 : ℝ)|=(1088504629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483807007/10000000000 : ℝ)|^8411 ≤ (34635839806383/100000000000000 : ℝ)^6363
        have hw : |(4483807007/10000000000 : ℝ)|=(4483807007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227925063/10000000000 : ℝ)|^8411 ≤ (16023682422357/50000000000000 : ℝ)^6363
        have hw : |(4227925063/10000000000 : ℝ)|=(4227925063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1218_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5711/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (707/6250 : ℝ) ^ (4205/1024 : ℝ) ≤ (811505202576213/6250000000000000000 : ℝ) := by
    have hpowers : (707/6250 : ℝ)^4205 ≤ (811505202576213/6250000000000000000 : ℝ)^1024 := by
      have hnat : (707 : ℕ)^4205*6250000000000000000^1024 ≤ 811505202576213^1024*6250^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 6250 811505202576213 6250000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/6250 : ℝ)) (X := (811505202576213/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4205/1024 : ℝ) ≤ (33375980746851387/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4205 ≤ (33375980746851387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4205*100000000000000000000^1024 ≤ 33375980746851387^1024*25000^4205 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 33375980746851387 100000000000000000000 4205 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (33375980746851387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125811505202576213/3125000000000000000 : ℝ) ≤ (10000632313698293/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (3125811505202576213/3125000000000000000 : ℝ)^1024 ≤ (10000632313698293/10000000000000000 : ℝ)^4205 := by
      have hnat : (3125811505202576213 : ℕ)^1024*10000000000000000^4205 ≤ 10000632313698293^4205*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125811505202576213 3125000000000000000 10000632313698293 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632313698293/10000000000000000 : ℝ)) (X := (3125811505202576213/3125000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009272012797614159/20000000000000000000 : ℝ) ≤ (500056438030119/500000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (20009272012797614159/20000000000000000000 : ℝ)^1024 ≤ (500056438030119/500000000000000 : ℝ)^4205 := by
      have hnat : (20009272012797614159 : ℕ)^1024*500000000000000^4205 ≤ 500056438030119^4205*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009272012797614159 20000000000000000000 500056438030119 500000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500056438030119/500000000000000 : ℝ)) (X := (20009272012797614159/20000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033375980746851387/50000000000000000000 : ℝ) ≤ (10001625207506467/10000000000000000 : ℝ) ^ (4205/1024 : ℝ) := by
    have hpowers : (50033375980746851387/50000000000000000000 : ℝ)^1024 ≤ (10001625207506467/10000000000000000 : ℝ)^4205 := by
      have hnat : (50033375980746851387 : ℕ)^1024*10000000000000000^4205 ≤ 10001625207506467^4205*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033375980746851387 50000000000000000000 10001625207506467 10000000000000000 1024 4205 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001625207506467/10000000000000000 : ℝ)) (X := (50033375980746851387/50000000000000000000 : ℝ)) (by norm_num) 4205 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(811505202576213/6250000000000000000 : ℝ) ≤ ((7307654317623936111/7310000000000000000 : ℝ)+2*(496446904087/292400000000000 : ℝ)*(707/6250 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (7307654317623936111/7310000000000000000 : ℝ)+2*(496446904087/292400000000000 : ℝ)*(707/6250 : ℝ)=(10000632313698293/10000000000000000 : ℝ) by norm_num, show 1+2*(811505202576213/6250000000000000000 : ℝ)=(3125811505202576213/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33375980746851387/100000000000000000000 : ℝ)+(811505202576213/6250000000000000000 : ℝ) ≤ ((7307654317623936111/7310000000000000000 : ℝ)+(496446904087/292400000000000 : ℝ)*((3559/25000 : ℝ)+(707/6250 : ℝ)))^(4205/1024 : ℝ) := by
    rw [show (7307654317623936111/7310000000000000000 : ℝ)+(496446904087/292400000000000 : ℝ)*((3559/25000 : ℝ)+(707/6250 : ℝ))=(500056438030119/500000000000000 : ℝ) by norm_num, show 1+(33375980746851387/100000000000000000000 : ℝ)+(811505202576213/6250000000000000000 : ℝ)=(20009272012797614159/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33375980746851387/100000000000000000000 : ℝ) ≤ ((7307654317623936111/7310000000000000000 : ℝ)+2*(496446904087/292400000000000 : ℝ)*(3559/25000 : ℝ))^(4205/1024 : ℝ) := by
    rw [show (7307654317623936111/7310000000000000000 : ℝ)+2*(496446904087/292400000000000 : ℝ)*(3559/25000 : ℝ)=(10001625207506467/10000000000000000 : ℝ) by norm_num, show 1+2*(33375980746851387/100000000000000000000 : ℝ)=(50033375980746851387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7307654317623936111/7310000000000000000 : ℝ)*(X 1 0+X 2 0)+(496446904087/292400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7307654317623936111/7310000000000000000 : ℝ)) (alpha := (496446904087/292400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7307654317623936111/7310000000000000000 : ℝ)*(X 0 1+X 2 1)+(496446904087/292400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7307654317623936111/7310000000000000000 : ℝ)) (alpha := (496446904087/292400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7307654317623936111/7310000000000000000 : ℝ)*(X 0 2+X 1 2)+(496446904087/292400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4205/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7307654317623936111/7310000000000000000 : ℝ)) (alpha := (496446904087/292400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130944363/10000000000 : ℝ)*X 0 0+(539299491/1000000000 : ℝ)*X 0 1+(526561231/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344773603/10000000000 : ℝ)*X 1 0+(-1097777613/5000000000 : ℝ)*X 1 1+(1316403077/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336193401/2500000000 : ℝ)*X 2 0+(329100769/625000000 : ℝ)*X 2 1+(-219555523/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177004087/5000000000 : ℝ)*X 0 0+(4227261097/10000000000 : ℝ)*X 0 1+(4484468747/10000000000 : ℝ)*X 0 2+(2177004087/5000000000 : ℝ)*X 1 0+(4227261097/10000000000 : ℝ)*X 1 1+(4484468747/10000000000 : ℝ)*X 1 2+(2177004087/5000000000 : ℝ)*X 2 0+(4227261097/10000000000 : ℝ)*X 2 1+(4484468747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130949439/10000000000 : ℝ)*X 0 0+(1316485007/2500000000 : ℝ)*X 0 1+(1348166483/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656162523/5000000000 : ℝ)*X 1 0+(-2068501399/10000000000 : ℝ)*X 1 1+(5392665963/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664040611/1250000000 : ℝ)*X 2 0+(5392666129/10000000000 : ℝ)*X 2 1+(-517125347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088504629/2500000000 : ℝ)*X 0 0+(4483807007/10000000000 : ℝ)*X 0 1+(4227925063/10000000000 : ℝ)*X 0 2+(1088504629/2500000000 : ℝ)*X 1 0+(4483807007/10000000000 : ℝ)*X 1 1+(4227925063/10000000000 : ℝ)*X 1 2+(1088504629/2500000000 : ℝ)*X 2 0+(4483807007/10000000000 : ℝ)*X 2 1+(4227925063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1218_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17231459800496432021187/2924000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1141370407/100000000000000 : ℝ)*(base19) + (212295411/20000000000000 : ℝ)*(base23) + (4348623/10000000000000 : ℝ)*(lower2) + (152248227/100000000000000 : ℝ)*(upper3) + (21526327/25000000000000 : ℝ)*(upper5) + (1173836911745663/20000000000000 : ℝ)*(major0) + (1173836911745663/20000000000000 : ℝ)*(major1) + (1173836911745663/20000000000000 : ℝ)*(major2) + (49064987453041/625000000000 : ℝ)*(sp0) + (1570085455066467/20000000000000 : ℝ)*(sp1) + (981303419403211/12500000000000 : ℝ)*(sp2) + (1943961973806577/50000000000000 : ℝ)*(sp3) + (30424216181/100000000000000 : ℝ)*(sp4) + (2069587957/12500000000000 : ℝ)*(sp7) + (388794050431681/10000000000000 : ℝ)*(f.failure) + (3925214208351371/50000000000000 : ℝ)*(f.sum) + (8555926436291/2924000000000000000000000000 : ℝ)*base66 + (243999556137238407/146200000000000000000000000000000 : ℝ)*base68 + (1015741887210761593/146200000000000000000000000000000 : ℝ)*base69 + (1171979885788961593/146200000000000000000000000000000 : ℝ)*base71 + (9597084668999/2924000000000000000000000000 : ℝ)*base74 + (2352556972414838407/146200000000000000000000000000000 : ℝ)*base76 + (512943907382438407/146200000000000000000000000000000 : ℝ)*base78 + (1648842708701961593/146200000000000000000000000000000 : ℝ)*base79 + (351751336257/2924000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (3869743/1000000000000000000000 : ℝ)*base89 + (3869743/1000000000000000000000 : ℝ)*base91 + (3869743/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12539044959304406633920113/5710937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (132322117/12500000000000 : ℝ)*(base19) + (960037633/100000000000000 : ℝ)*(base23) + (161087697/100000000000000 : ℝ)*(upper3) + (13361511/25000000000000 : ℝ)*(lower4) + (67756333/100000000000000 : ℝ)*(upper5) + (184360793792553/3125000000000 : ℝ)*(major0) + (184360793792553/3125000000000 : ℝ)*(major1) + (184360793792553/3125000000000 : ℝ)*(major2) + (27633701377/100000000000000 : ℝ)*(sp1) + (8363384647/25000000000000 : ℝ)*(sp2) + (7891038206481673/100000000000000 : ℝ)*(sp4) + (49318809463771/625000000000 : ℝ)*(sp5) + (7891003792905451/100000000000000 : ℝ)*(sp6) + (1954026261527199/50000000000000 : ℝ)*(sp7) + (1954026261527199/50000000000000 : ℝ)*(f.failure) + (7891038206481673/100000000000000 : ℝ)*(f.sum) + (11147734391633/3655000000000000000000000000 : ℝ)*base65 + (45933051577043883/22843750000000000000000000000000 : ℝ)*base67 + (62938677387043883/22843750000000000000000000000000 : ℝ)*base69 + (103978272635424867/22843750000000000000000000000000 : ℝ)*base72 + (37876206089/7138671875000000000000000 : ℝ)*base73 + (33458371188293883/22843750000000000000000000000000 : ℝ)*base75 + (5208516589143617/22843750000000000000000000000000 : ℝ)*base78 + (353874817745887633/22843750000000000000000000000000 : ℝ)*base79 + (7686461702121/1827500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (39737103/5000000000000000000000 : ℝ)*base90 + (39737103/5000000000000000000000 : ℝ)*base92 + (39737103/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1218_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1218_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1218_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1218_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1218_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1218_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4205/1024 : ℝ) ≤ p) (hpb : p ≤ (8411/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150958703/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1218_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
