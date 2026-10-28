-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:12.814987+00:00
-- url     : https://prove2.me/submissions/96ffd704-9508-473c-8139-60e3ea774979

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
theorem support_rectangle_w1214_s3_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-266229819/1250000000 : ℝ)*x 0 + (5422161709/10000000000 : ℝ)*x 1 + (1047681273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266229819/1250000000 : ℝ)^8407 ≤ (3235726938257/25000000000000 : ℝ)^6359 := by
    have hnat : (266229819 : ℕ)^8407*25000000000000^6359 ≤ 3235726938257^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266229819 1250000000 3235726938257 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422161709/10000000000 : ℝ)^8407 ≤ (8904082810071/20000000000000 : ℝ)^6359 := by
    have hnat : (5422161709 : ℕ)^8407*20000000000000^6359 ≤ 8904082810071^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422161709 10000000000 8904082810071 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047681273/2000000000 : ℝ)^8407 ≤ (10634169547801/25000000000000 : ℝ)^6359 := by
    have hnat : (1047681273 : ℕ)^8407*25000000000000^6359 ≤ 10634169547801^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047681273 2000000000 10634169547801 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266229819/1250000000 : ℝ), (5422161709/10000000000 : ℝ), (1047681273/2000000000 : ℝ)] ![(3235726938257/25000000000000 : ℝ), (8904082810071/20000000000000 : ℝ), (10634169547801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266229819/1250000000 : ℝ)|^8407 ≤ (3235726938257/25000000000000 : ℝ)^6359
        have hw : |(-266229819/1250000000 : ℝ)|=(266229819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422161709/10000000000 : ℝ)|^8407 ≤ (8904082810071/20000000000000 : ℝ)^6359
        have hw : |(5422161709/10000000000 : ℝ)|=(5422161709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047681273/2000000000 : ℝ)|^8407 ≤ (10634169547801/25000000000000 : ℝ)^6359
        have hw : |(1047681273/2000000000 : ℝ)|=(1047681273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669014103/1250000000 : ℝ)*x 0 + (-2223628499/10000000000 : ℝ)*x 1 + (2619203221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669014103/1250000000 : ℝ)^8407 ≤ (5470200497087/12500000000000 : ℝ)^6359 := by
    have hnat : (669014103 : ℕ)^8407*12500000000000^6359 ≤ 5470200497087^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669014103 1250000000 5470200497087 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2223628499/10000000000 : ℝ)^8407 ≤ (856357312037/6250000000000 : ℝ)^6359 := by
    have hnat : (2223628499 : ℕ)^8407*6250000000000^6359 ≤ 856357312037^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223628499 10000000000 856357312037 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619203221/5000000000 : ℝ)^8407 ≤ (42536679017827/100000000000000 : ℝ)^6359 := by
    have hnat : (2619203221 : ℕ)^8407*100000000000000^6359 ≤ 42536679017827^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619203221 5000000000 42536679017827 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669014103/1250000000 : ℝ), (-2223628499/10000000000 : ℝ), (2619203221/5000000000 : ℝ)] ![(5470200497087/12500000000000 : ℝ), (856357312037/6250000000000 : ℝ), (42536679017827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669014103/1250000000 : ℝ)|^8407 ≤ (5470200497087/12500000000000 : ℝ)^6359
        have hw : |(669014103/1250000000 : ℝ)|=(669014103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2223628499/10000000000 : ℝ)|^8407 ≤ (856357312037/6250000000000 : ℝ)^6359
        have hw : |(-2223628499/10000000000 : ℝ)|=(2223628499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619203221/5000000000 : ℝ)|^8407 ≤ (42536679017827/100000000000000 : ℝ)^6359
        have hw : |(2619203221/5000000000 : ℝ)|=(2619203221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1338028191/2500000000 : ℝ)*x 0 + (5238406639/10000000000 : ℝ)*x 1 + (-1111814159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338028191/2500000000 : ℝ)^8407 ≤ (5470200416013/12500000000000 : ℝ)^6359 := by
    have hnat : (1338028191 : ℕ)^8407*12500000000000^6359 ≤ 5470200416013^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338028191 2500000000 5470200416013 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238406639/10000000000 : ℝ)^8407 ≤ (42536681132693/100000000000000 : ℝ)^6359 := by
    have hnat : (5238406639 : ℕ)^8407*100000000000000^6359 ≤ 42536681132693^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238406639 10000000000 42536681132693 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111814159/5000000000 : ℝ)^8407 ≤ (856357219881/6250000000000 : ℝ)^6359 := by
    have hnat : (1111814159 : ℕ)^8407*6250000000000^6359 ≤ 856357219881^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111814159 5000000000 856357219881 6250000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338028191/2500000000 : ℝ), (5238406639/10000000000 : ℝ), (-1111814159/5000000000 : ℝ)] ![(5470200416013/12500000000000 : ℝ), (42536681132693/100000000000000 : ℝ), (856357219881/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338028191/2500000000 : ℝ)|^8407 ≤ (5470200416013/12500000000000 : ℝ)^6359
        have hw : |(1338028191/2500000000 : ℝ)|=(1338028191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238406639/10000000000 : ℝ)|^8407 ≤ (42536681132693/100000000000000 : ℝ)^6359
        have hw : |(5238406639/10000000000 : ℝ)|=(5238406639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111814159/5000000000 : ℝ)|^8407 ≤ (856357219881/6250000000000 : ℝ)^6359
        have hw : |(-1111814159/5000000000 : ℝ)|=(1111814159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352788567/10000000000 : ℝ)*x 0 + (2085636963/5000000000 : ℝ)*x 1 + (2271009901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352788567/10000000000 : ℝ)^8407 ≤ (16649373595623/50000000000000 : ℝ)^6359 := by
    have hnat : (4352788567 : ℕ)^8407*50000000000000^6359 ≤ 16649373595623^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352788567 10000000000 16649373595623 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085636963/5000000000 : ℝ)^8407 ≤ (31475397968019/100000000000000 : ℝ)^6359 := by
    have hnat : (2085636963 : ℕ)^8407*100000000000000^6359 ≤ 31475397968019^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085636963 5000000000 31475397968019 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271009901/5000000000 : ℝ)^8407 ≤ (704517096531/2000000000000 : ℝ)^6359 := by
    have hnat : (2271009901 : ℕ)^8407*2000000000000^6359 ≤ 704517096531^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271009901 5000000000 704517096531 2000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352788567/10000000000 : ℝ), (2085636963/5000000000 : ℝ), (2271009901/5000000000 : ℝ)] ![(16649373595623/50000000000000 : ℝ), (31475397968019/100000000000000 : ℝ), (704517096531/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352788567/10000000000 : ℝ)|^8407 ≤ (16649373595623/50000000000000 : ℝ)^6359
        have hw : |(4352788567/10000000000 : ℝ)|=(4352788567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085636963/5000000000 : ℝ)|^8407 ≤ (31475397968019/100000000000000 : ℝ)^6359
        have hw : |(2085636963/5000000000 : ℝ)|=(2085636963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271009901/5000000000 : ℝ)|^8407 ≤ (704517096531/2000000000000 : ℝ)^6359
        have hw : |(2271009901/5000000000 : ℝ)|=(2271009901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064926793/5000000000 : ℝ)*x 0 + (26195429/50000000 : ℝ)*x 1 + (5421478621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064926793/5000000000 : ℝ)^8407 ≤ (1294302853787/10000000000000 : ℝ)^6359 := by
    have hnat : (1064926793 : ℕ)^8407*10000000000000^6359 ≤ 1294302853787^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064926793 5000000000 1294302853787 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26195429/50000000 : ℝ)^8407 ≤ (42543972322797/100000000000000 : ℝ)^6359 := by
    have hnat : (26195429 : ℕ)^8407*100000000000000^6359 ≤ 42543972322797^6359*50000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26195429 50000000 42543972322797 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421478621/10000000000 : ℝ)^8407 ≤ (22256499562387/50000000000000 : ℝ)^6359 := by
    have hnat : (5421478621 : ℕ)^8407*50000000000000^6359 ≤ 22256499562387^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421478621 10000000000 22256499562387 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064926793/5000000000 : ℝ), (26195429/50000000 : ℝ), (5421478621/10000000000 : ℝ)] ![(1294302853787/10000000000000 : ℝ), (42543972322797/100000000000000 : ℝ), (22256499562387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064926793/5000000000 : ℝ)|^8407 ≤ (1294302853787/10000000000000 : ℝ)^6359
        have hw : |(-1064926793/5000000000 : ℝ)|=(1064926793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26195429/50000000 : ℝ)|^8407 ≤ (42543972322797/100000000000000 : ℝ)^6359
        have hw : |(26195429/50000000 : ℝ)|=(26195429/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421478621/10000000000 : ℝ)|^8407 ≤ (22256499562387/50000000000000 : ℝ)^6359
        have hw : |(5421478621/10000000000 : ℝ)|=(5421478621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305321527/10000000000 : ℝ)*x 0 + (-2040556389/10000000000 : ℝ)*x 1 + (677684787/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305321527/10000000000 : ℝ)^8407 ≤ (43256509965797/100000000000000 : ℝ)^6359 := by
    have hnat : (5305321527 : ℕ)^8407*100000000000000^6359 ≤ 43256509965797^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305321527 10000000000 43256509965797 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040556389/10000000000 : ℝ)^8407 ≤ (6115247213403/50000000000000 : ℝ)^6359 := by
    have hnat : (2040556389 : ℕ)^8407*50000000000000^6359 ≤ 6115247213403^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040556389 10000000000 6115247213403 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677684787/1250000000 : ℝ)^8407 ≤ (5564124449621/12500000000000 : ℝ)^6359 := by
    have hnat : (677684787 : ℕ)^8407*12500000000000^6359 ≤ 5564124449621^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677684787 1250000000 5564124449621 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305321527/10000000000 : ℝ), (-2040556389/10000000000 : ℝ), (677684787/1250000000 : ℝ)] ![(43256509965797/100000000000000 : ℝ), (6115247213403/50000000000000 : ℝ), (5564124449621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305321527/10000000000 : ℝ)|^8407 ≤ (43256509965797/100000000000000 : ℝ)^6359
        have hw : |(5305321527/10000000000 : ℝ)|=(5305321527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040556389/10000000000 : ℝ)|^8407 ≤ (6115247213403/50000000000000 : ℝ)^6359
        have hw : |(-2040556389/10000000000 : ℝ)|=(2040556389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677684787/1250000000 : ℝ)|^8407 ≤ (5564124449621/12500000000000 : ℝ)^6359
        have hw : |(677684787/1250000000 : ℝ)|=(677684787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305321379/10000000000 : ℝ)*x 0 + (1084295657/2000000000 : ℝ)*x 1 + (-408111321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305321379/10000000000 : ℝ)^8407 ≤ (5407063546307/12500000000000 : ℝ)^6359 := by
    have hnat : (5305321379 : ℕ)^8407*12500000000000^6359 ≤ 5407063546307^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305321379 10000000000 5407063546307 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084295657/2000000000 : ℝ)^8407 ≤ (8902599095513/20000000000000 : ℝ)^6359 := by
    have hnat : (1084295657 : ℕ)^8407*20000000000000^6359 ≤ 8902599095513^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084295657 2000000000 8902599095513 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408111321/2000000000 : ℝ)^8407 ≤ (6115248069201/50000000000000 : ℝ)^6359 := by
    have hnat : (408111321 : ℕ)^8407*50000000000000^6359 ≤ 6115248069201^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408111321 2000000000 6115248069201 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305321379/10000000000 : ℝ), (1084295657/2000000000 : ℝ), (-408111321/2000000000 : ℝ)] ![(5407063546307/12500000000000 : ℝ), (8902599095513/20000000000000 : ℝ), (6115248069201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305321379/10000000000 : ℝ)|^8407 ≤ (5407063546307/12500000000000 : ℝ)^6359
        have hw : |(5305321379/10000000000 : ℝ)|=(5305321379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084295657/2000000000 : ℝ)|^8407 ≤ (8902599095513/20000000000000 : ℝ)^6359
        have hw : |(1084295657/2000000000 : ℝ)|=(1084295657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408111321/2000000000 : ℝ)|^8407 ≤ (6115248069201/50000000000000 : ℝ)^6359
        have hw : |(-408111321/2000000000 : ℝ)|=(408111321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s3_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435281903/1000000000 : ℝ)*x 0 + (4540648489/10000000000 : ℝ)*x 1 + (208632617/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435281903/1000000000 : ℝ)^8407 ≤ (16649527643497/50000000000000 : ℝ)^6359 := by
    have hnat : (435281903 : ℕ)^8407*50000000000000^6359 ≤ 16649527643497^6359*1000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435281903 1000000000 16649527643497 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540648489/10000000000 : ℝ)^8407 ≤ (35211794991789/100000000000000 : ℝ)^6359 := by
    have hnat : (4540648489 : ℕ)^8407*100000000000000^6359 ≤ 35211794991789^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540648489 10000000000 35211794991789 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208632617/500000000 : ℝ)^8407 ≤ (15744574851989/50000000000000 : ℝ)^6359 := by
    have hnat : (208632617 : ℕ)^8407*50000000000000^6359 ≤ 15744574851989^6359*500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208632617 500000000 15744574851989 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435281903/1000000000 : ℝ), (4540648489/10000000000 : ℝ), (208632617/500000000 : ℝ)] ![(16649527643497/50000000000000 : ℝ), (35211794991789/100000000000000 : ℝ), (15744574851989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435281903/1000000000 : ℝ)|^8407 ≤ (16649527643497/50000000000000 : ℝ)^6359
        have hw : |(435281903/1000000000 : ℝ)|=(435281903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540648489/10000000000 : ℝ)|^8407 ≤ (35211794991789/100000000000000 : ℝ)^6359
        have hw : |(4540648489/10000000000 : ℝ)|=(4540648489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208632617/500000000 : ℝ)|^8407 ≤ (15744574851989/50000000000000 : ℝ)^6359
        have hw : |(208632617/500000000 : ℝ)|=(208632617/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5419/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14727/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16297/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1173/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16297/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1173/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16297/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1173/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16297/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1173/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16297/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1173/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16297/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1173/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1173/12500 : ℝ) ^ (4203/1024 : ℝ) ≤ (6055842486364693/100000000000000000000 : ℝ) := by
    have hpowers : (1173/12500 : ℝ)^4203 ≤ (6055842486364693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1173 : ℕ)^4203*100000000000000000000^1024 ≤ 6055842486364693^1024*12500^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1173 12500 6055842486364693 100000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1173/12500 : ℝ)) (X := (6055842486364693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16297/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (1167164485355811/2000000000000000000 : ℝ) := by
    have hpowers : (16297/100000 : ℝ)^4203 ≤ (1167164485355811/2000000000000000000 : ℝ)^1024 := by
      have hnat : (16297 : ℕ)^4203*2000000000000000000^1024 ≤ 1167164485355811^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16297 100000 1167164485355811 2000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16297/100000 : ℝ)) (X := (1167164485355811/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006055842486364693/50000000000000000000 : ℝ) ≤ (500014753506271/500000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50006055842486364693/50000000000000000000 : ℝ)^1024 ≤ (500014753506271/500000000000000 : ℝ)^4203 := by
      have hnat : (50006055842486364693 : ℕ)^1024*500000000000000^4203 ≤ 500014753506271^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006055842486364693 50000000000000000000 500014753506271 500000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014753506271/500000000000000 : ℝ)) (X := (50006055842486364693/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100064414066754155243/100000000000000000000 : ℝ) ≤ (10001568973171227/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (100064414066754155243/100000000000000000000 : ℝ)^1024 ≤ (10001568973171227/10000000000000000 : ℝ)^4203 := by
      have hnat : (100064414066754155243 : ℕ)^1024*10000000000000000^4203 ≤ 10001568973171227^4203*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100064414066754155243 100000000000000000000 10001568973171227 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001568973171227/10000000000000000 : ℝ)) (X := (100064414066754155243/100000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1001167164485355811/1000000000000000000 : ℝ) ≤ (5001421438108517/5000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (1001167164485355811/1000000000000000000 : ℝ)^1024 ≤ (5001421438108517/5000000000000000 : ℝ)^4203 := by
      have hnat : (1001167164485355811 : ℕ)^1024*5000000000000000^4203 ≤ 5001421438108517^4203*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001167164485355811 1000000000000000000 5001421438108517 5000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001421438108517/5000000000000000 : ℝ)) (X := (1001167164485355811/1000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6055842486364693/100000000000000000000 : ℝ) ≤ ((17277032801853330671/17282500000000000000 : ℝ)+2*(1273903045807/691300000000000 : ℝ)*(1173/12500 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (17277032801853330671/17282500000000000000 : ℝ)+2*(1273903045807/691300000000000 : ℝ)*(1173/12500 : ℝ)=(500014753506271/500000000000000 : ℝ) by norm_num, show 1+2*(6055842486364693/100000000000000000000 : ℝ)=(50006055842486364693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1167164485355811/2000000000000000000 : ℝ)+(6055842486364693/100000000000000000000 : ℝ) ≤ ((17277032801853330671/17282500000000000000 : ℝ)+(1273903045807/691300000000000 : ℝ)*((16297/100000 : ℝ)+(1173/12500 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (17277032801853330671/17282500000000000000 : ℝ)+(1273903045807/691300000000000 : ℝ)*((16297/100000 : ℝ)+(1173/12500 : ℝ))=(10001568973171227/10000000000000000 : ℝ) by norm_num, show 1+(1167164485355811/2000000000000000000 : ℝ)+(6055842486364693/100000000000000000000 : ℝ)=(100064414066754155243/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1167164485355811/2000000000000000000 : ℝ) ≤ ((17277032801853330671/17282500000000000000 : ℝ)+2*(1273903045807/691300000000000 : ℝ)*(16297/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (17277032801853330671/17282500000000000000 : ℝ)+2*(1273903045807/691300000000000 : ℝ)*(16297/100000 : ℝ)=(5001421438108517/5000000000000000 : ℝ) by norm_num, show 1+2*(1167164485355811/2000000000000000000 : ℝ)=(1001167164485355811/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17277032801853330671/17282500000000000000 : ℝ)*(X 1 0+X 2 0)+(1273903045807/691300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (1173/12500 : ℝ)) (hi := (16297/100000 : ℝ)) (c := (17277032801853330671/17282500000000000000 : ℝ)) (alpha := (1273903045807/691300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17277032801853330671/17282500000000000000 : ℝ)*(X 0 1+X 2 1)+(1273903045807/691300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (1173/12500 : ℝ)) (hi := (16297/100000 : ℝ)) (c := (17277032801853330671/17282500000000000000 : ℝ)) (alpha := (1273903045807/691300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17277032801853330671/17282500000000000000 : ℝ)*(X 0 2+X 1 2)+(1273903045807/691300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (1173/12500 : ℝ)) (hi := (16297/100000 : ℝ)) (c := (17277032801853330671/17282500000000000000 : ℝ)) (alpha := (1273903045807/691300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-266229819/1250000000 : ℝ)*X 0 0+(5422161709/10000000000 : ℝ)*X 0 1+(1047681273/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669014103/1250000000 : ℝ)*X 1 0+(-2223628499/10000000000 : ℝ)*X 1 1+(2619203221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338028191/2500000000 : ℝ)*X 2 0+(5238406639/10000000000 : ℝ)*X 2 1+(-1111814159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352788567/10000000000 : ℝ)*X 0 0+(2085636963/5000000000 : ℝ)*X 0 1+(2271009901/5000000000 : ℝ)*X 0 2+(4352788567/10000000000 : ℝ)*X 1 0+(2085636963/5000000000 : ℝ)*X 1 1+(2271009901/5000000000 : ℝ)*X 1 2+(4352788567/10000000000 : ℝ)*X 2 0+(2085636963/5000000000 : ℝ)*X 2 1+(2271009901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064926793/5000000000 : ℝ)*X 0 0+(26195429/50000000 : ℝ)*X 0 1+(5421478621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305321527/10000000000 : ℝ)*X 1 0+(-2040556389/10000000000 : ℝ)*X 1 1+(677684787/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305321379/10000000000 : ℝ)*X 2 0+(1084295657/2000000000 : ℝ)*X 2 1+(-408111321/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435281903/1000000000 : ℝ)*X 0 0+(4540648489/10000000000 : ℝ)*X 0 1+(208632617/500000000 : ℝ)*X 0 2+(435281903/1000000000 : ℝ)*X 1 0+(4540648489/10000000000 : ℝ)*X 1 1+(208632617/500000000 : ℝ)*X 1 2+(435281903/1000000000 : ℝ)*X 2 0+(4540648489/10000000000 : ℝ)*X 2 1+(208632617/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (236030158539399626250231/34565000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1121781653/100000000000000 : ℝ)*(base19) + (449700169/50000000000000 : ℝ)*(base23) + (8636857/10000000000000 : ℝ)*(lower2) + (63232171/100000000000000 : ℝ)*(upper3) + (33273599/25000000000000 : ℝ)*(upper5) + (1017419796664029/25000000000000 : ℝ)*(major0) + (1017419796664029/25000000000000 : ℝ)*(major1) + (1017419796664029/25000000000000 : ℝ)*(major2) + (5442042674578677/100000000000000 : ℝ)*(sp0) + (5442069564611321/100000000000000 : ℝ)*(sp1) + (1360517446748159/25000000000000 : ℝ)*(sp2) + (539455327688799/20000000000000 : ℝ)*(sp3) + (28011814297/100000000000000 : ℝ)*(sp4) + (2705213911/25000000000000 : ℝ)*(sp7) + (2697287459299639/100000000000000 : ℝ)*(f.failure) + (2721035343196487/50000000000000 : ℝ)*(f.sum) + (129348610387077/34565000000000000000000000000 : ℝ)*base65 + (1875103306742770959/432062500000000000000000000000000 : ℝ)*base67 + (2560692970174041541/432062500000000000000000000000000 : ℝ)*base70 + (3277169898846604041/432062500000000000000000000000000 : ℝ)*base72 + (50673630327843/34565000000000000000000000000 : ℝ)*base74 + (2946027265549708459/432062500000000000000000000000000 : ℝ)*base75 + (3540695791984104041/432062500000000000000000000000000 : ℝ)*base78 + (4260283248590083459/432062500000000000000000000000000 : ℝ)*base79 + (26941851222009/17282500000000000000000000000 : ℝ)*base82 + (604029/250000000000000000000 : ℝ)*base89 + (604029/250000000000000000000 : ℝ)*base91 + (604029/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32392030370270770170764211/6750976562500000000000000000000 : ℝ) := by norm_num
    linear_combination (1164664357/100000000000000 : ℝ)*(base19) + (355899/31250000000 : ℝ)*(base23) + (107649677/100000000000000 : ℝ)*(lower4) + (3039771/1562500000000 : ℝ)*(upper5) + (512506032650891/12500000000000 : ℝ)*(major0) + (512506032650891/12500000000000 : ℝ)*(major1) + (512506032650891/12500000000000 : ℝ)*(major2) + (3009854409/100000000000000 : ℝ)*(sp0) + (22404266207/100000000000000 : ℝ)*(sp1) + (6907823369/50000000000000 : ℝ)*(sp2) + (685334748298073/12500000000000 : ℝ)*(sp4) + (5482657427308429/100000000000000 : ℝ)*(sp5) + (1096533208343091/20000000000000 : ℝ)*(sp6) + (2717415366237749/100000000000000 : ℝ)*(sp7) + (2717415366237749/100000000000000 : ℝ)*(f.failure) + (5482680996238993/100000000000000 : ℝ)*(f.sum) + (32869469202613/17282500000000000000000000000 : ℝ)*base65 + (2034441601122140361/216031250000000000000000000000000 : ℝ)*base67 + (936888102451171611/216031250000000000000000000000000 : ℝ)*base69 + (2453799372655671611/216031250000000000000000000000000 : ℝ)*base71 + (68310380530141/34565000000000000000000000000 : ℝ)*base73 + (1480385887858140361/216031250000000000000000000000000 : ℝ)*base75 + (1638457118107609111/216031250000000000000000000000000 : ℝ)*base77 + (1098733333828765361/216031250000000000000000000000000 : ℝ)*base79 + (47653487442769/34565000000000000000000000000 : ℝ)*base82 + (2156761/250000000000000000000 : ℝ)*base90 + (2156761/250000000000000000000 : ℝ)*base92 + (2156761/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5419/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1214_s4_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066155149/5000000000 : ℝ)*x 0 + (1079729507/2000000000 : ℝ)*x 1 + (5260301603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066155149/5000000000 : ℝ)^8407 ≤ (1296276972513/10000000000000 : ℝ)^6359 := by
    have hnat : (1066155149 : ℕ)^8407*10000000000000^6359 ≤ 1296276972513^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066155149 5000000000 1296276972513 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079729507/2000000000 : ℝ)^8407 ≤ (8853068151483/20000000000000 : ℝ)^6359 := by
    have hnat : (1079729507 : ℕ)^8407*20000000000000^6359 ≤ 8853068151483^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079729507 2000000000 8853068151483 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260301603/10000000000 : ℝ)^8407 ≤ (2138594475493/5000000000000 : ℝ)^6359 := by
    have hnat : (5260301603 : ℕ)^8407*5000000000000^6359 ≤ 2138594475493^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260301603 10000000000 2138594475493 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066155149/5000000000 : ℝ), (1079729507/2000000000 : ℝ), (5260301603/10000000000 : ℝ)] ![(1296276972513/10000000000000 : ℝ), (8853068151483/20000000000000 : ℝ), (2138594475493/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066155149/5000000000 : ℝ)|^8407 ≤ (1296276972513/10000000000000 : ℝ)^6359
        have hw : |(-1066155149/5000000000 : ℝ)|=(1066155149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079729507/2000000000 : ℝ)|^8407 ≤ (8853068151483/20000000000000 : ℝ)^6359
        have hw : |(1079729507/2000000000 : ℝ)|=(1079729507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260301603/10000000000 : ℝ)|^8407 ≤ (2138594475493/5000000000000 : ℝ)^6359
        have hw : |(5260301603/10000000000 : ℝ)|=(5260301603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346200777/10000000000 : ℝ)*x 0 + (-550641779/2500000000 : ℝ)*x 1 + (263015073/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346200777/10000000000 : ℝ)^8407 ≤ (43697706928729/100000000000000 : ℝ)^6359 := by
    have hnat : (5346200777 : ℕ)^8407*100000000000000^6359 ≤ 43697706928729^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346200777 10000000000 43697706928729 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550641779/2500000000 : ℝ)^8407 ≤ (6765202544927/50000000000000 : ℝ)^6359 := by
    have hnat : (550641779 : ℕ)^8407*50000000000000^6359 ≤ 6765202544927^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550641779 2500000000 6765202544927 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263015073/500000000 : ℝ)^8407 ≤ (267324299829/625000000000 : ℝ)^6359 := by
    have hnat : (263015073 : ℕ)^8407*625000000000^6359 ≤ 267324299829^6359*500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263015073 500000000 267324299829 625000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346200777/10000000000 : ℝ), (-550641779/2500000000 : ℝ), (263015073/500000000 : ℝ)] ![(43697706928729/100000000000000 : ℝ), (6765202544927/50000000000000 : ℝ), (267324299829/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346200777/10000000000 : ℝ)|^8407 ≤ (43697706928729/100000000000000 : ℝ)^6359
        have hw : |(5346200777/10000000000 : ℝ)|=(5346200777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550641779/2500000000 : ℝ)|^8407 ≤ (6765202544927/50000000000000 : ℝ)^6359
        have hw : |(-550641779/2500000000 : ℝ)|=(550641779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263015073/500000000 : ℝ)|^8407 ≤ (267324299829/625000000000 : ℝ)^6359
        have hw : |(263015073/500000000 : ℝ)|=(263015073/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673100111/5000000000 : ℝ)*x 0 + (1315075371/2500000000 : ℝ)*x 1 + (-2202567821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673100111/5000000000 : ℝ)^8407 ≤ (4369770093139/10000000000000 : ℝ)^6359 := by
    have hnat : (2673100111 : ℕ)^8407*10000000000000^6359 ≤ 4369770093139^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673100111 5000000000 4369770093139 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315075371/2500000000 : ℝ)^8407 ≤ (8554377646127/20000000000000 : ℝ)^6359 := by
    have hnat : (1315075371 : ℕ)^8407*20000000000000^6359 ≤ 8554377646127^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315075371 2500000000 8554377646127 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202567821/10000000000 : ℝ)^8407 ≤ (13530410815481/100000000000000 : ℝ)^6359 := by
    have hnat : (2202567821 : ℕ)^8407*100000000000000^6359 ≤ 13530410815481^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202567821 10000000000 13530410815481 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673100111/5000000000 : ℝ), (1315075371/2500000000 : ℝ), (-2202567821/10000000000 : ℝ)] ![(4369770093139/10000000000000 : ℝ), (8554377646127/20000000000000 : ℝ), (13530410815481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673100111/5000000000 : ℝ)|^8407 ≤ (4369770093139/10000000000000 : ℝ)^6359
        have hw : |(2673100111/5000000000 : ℝ)|=(2673100111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315075371/2500000000 : ℝ)|^8407 ≤ (8554377646127/20000000000000 : ℝ)^6359
        have hw : |(1315075371/2500000000 : ℝ)|=(1315075371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202567821/10000000000 : ℝ)|^8407 ≤ (13530410815481/100000000000000 : ℝ)^6359
        have hw : |(-2202567821/10000000000 : ℝ)|=(2202567821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870853637/2000000000 : ℝ)*x 0 + (4216893703/10000000000 : ℝ)*x 1 + (4496021371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870853637/2000000000 : ℝ)^8407 ≤ (16656856254123/50000000000000 : ℝ)^6359 := by
    have hnat : (870853637 : ℕ)^8407*50000000000000^6359 ≤ 16656856254123^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870853637 2000000000 16656856254123 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216893703/10000000000 : ℝ)^8407 ≤ (15965649305609/50000000000000 : ℝ)^6359 := by
    have hnat : (4216893703 : ℕ)^8407*50000000000000^6359 ≤ 15965649305609^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216893703 10000000000 15965649305609 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4496021371/10000000000 : ℝ)^8407 ≤ (1086093402093/3125000000000 : ℝ)^6359 := by
    have hnat : (4496021371 : ℕ)^8407*3125000000000^6359 ≤ 1086093402093^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496021371 10000000000 1086093402093 3125000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870853637/2000000000 : ℝ), (4216893703/10000000000 : ℝ), (4496021371/10000000000 : ℝ)] ![(16656856254123/50000000000000 : ℝ), (15965649305609/50000000000000 : ℝ), (1086093402093/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870853637/2000000000 : ℝ)|^8407 ≤ (16656856254123/50000000000000 : ℝ)^6359
        have hw : |(870853637/2000000000 : ℝ)|=(870853637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216893703/10000000000 : ℝ)|^8407 ≤ (15965649305609/50000000000000 : ℝ)^6359
        have hw : |(4216893703/10000000000 : ℝ)|=(4216893703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4496021371/10000000000 : ℝ)|^8407 ≤ (1086093402093/3125000000000 : ℝ)^6359
        have hw : |(4496021371/10000000000 : ℝ)|=(4496021371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132316679/10000000000 : ℝ)*x 0 + (1315171939/2500000000 : ℝ)*x 1 + (337391241/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132316679/10000000000 : ℝ)^8407 ≤ (5063601957/39062500000 : ℝ)^6359 := by
    have hnat : (2132316679 : ℕ)^8407*39062500000^6359 ≤ 5063601957^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132316679 10000000000 5063601957 39062500000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315171939/2500000000 : ℝ)^8407 ≤ (42776040622903/100000000000000 : ℝ)^6359 := by
    have hnat : (1315171939 : ℕ)^8407*100000000000000^6359 ≤ 42776040622903^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315171939 2500000000 42776040622903 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337391241/625000000 : ℝ)^8407 ≤ (885222766969/2000000000000 : ℝ)^6359 := by
    have hnat : (337391241 : ℕ)^8407*2000000000000^6359 ≤ 885222766969^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337391241 625000000 885222766969 2000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132316679/10000000000 : ℝ), (1315171939/2500000000 : ℝ), (337391241/625000000 : ℝ)] ![(5063601957/39062500000 : ℝ), (42776040622903/100000000000000 : ℝ), (885222766969/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132316679/10000000000 : ℝ)|^8407 ≤ (5063601957/39062500000 : ℝ)^6359
        have hw : |(-2132316679/10000000000 : ℝ)|=(2132316679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315171939/2500000000 : ℝ)|^8407 ≤ (42776040622903/100000000000000 : ℝ)^6359
        have hw : |(1315171939/2500000000 : ℝ)|=(1315171939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337391241/625000000 : ℝ)|^8407 ≤ (885222766969/2000000000000 : ℝ)^6359
        have hw : |(337391241/625000000 : ℝ)|=(337391241/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310970053/10000000000 : ℝ)*x 0 + (-2064609203/10000000000 : ℝ)*x 1 + (5398260109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310970053/10000000000 : ℝ)^8407 ≤ (2165870387963/5000000000000 : ℝ)^6359 := by
    have hnat : (5310970053 : ℕ)^8407*5000000000000^6359 ≤ 2165870387963^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310970053 10000000000 2165870387963 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064609203/10000000000 : ℝ)^8407 ≤ (12421451134599/100000000000000 : ℝ)^6359 := by
    have hnat : (2064609203 : ℕ)^8407*100000000000000^6359 ≤ 12421451134599^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064609203 10000000000 12421451134599 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398260109/10000000000 : ℝ)^8407 ≤ (44261141090917/100000000000000 : ℝ)^6359 := by
    have hnat : (5398260109 : ℕ)^8407*100000000000000^6359 ≤ 44261141090917^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398260109 10000000000 44261141090917 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310970053/10000000000 : ℝ), (-2064609203/10000000000 : ℝ), (5398260109/10000000000 : ℝ)] ![(2165870387963/5000000000000 : ℝ), (12421451134599/100000000000000 : ℝ), (44261141090917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310970053/10000000000 : ℝ)|^8407 ≤ (2165870387963/5000000000000 : ℝ)^6359
        have hw : |(5310970053/10000000000 : ℝ)|=(5310970053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064609203/10000000000 : ℝ)|^8407 ≤ (12421451134599/100000000000000 : ℝ)^6359
        have hw : |(-2064609203/10000000000 : ℝ)|=(2064609203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398260109/10000000000 : ℝ)|^8407 ≤ (44261141090917/100000000000000 : ℝ)^6359
        have hw : |(5398260109/10000000000 : ℝ)|=(5398260109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062194017/2000000000 : ℝ)*x 0 + (1349565113/2500000000 : ℝ)*x 1 + (-2064608691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062194017/2000000000 : ℝ)^8407 ≤ (43317408104317/100000000000000 : ℝ)^6359 := by
    have hnat : (1062194017 : ℕ)^8407*100000000000000^6359 ≤ 43317408104317^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062194017 2000000000 43317408104317 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349565113/2500000000 : ℝ)^8407 ≤ (44261144808967/100000000000000 : ℝ)^6359 := by
    have hnat : (1349565113 : ℕ)^8407*100000000000000^6359 ≤ 44261144808967^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349565113 2500000000 44261144808967 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064608691/10000000000 : ℝ)^8407 ≤ (12421447062141/100000000000000 : ℝ)^6359 := by
    have hnat : (2064608691 : ℕ)^8407*100000000000000^6359 ≤ 12421447062141^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064608691 10000000000 12421447062141 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062194017/2000000000 : ℝ), (1349565113/2500000000 : ℝ), (-2064608691/10000000000 : ℝ)] ![(43317408104317/100000000000000 : ℝ), (44261144808967/100000000000000 : ℝ), (12421447062141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062194017/2000000000 : ℝ)|^8407 ≤ (43317408104317/100000000000000 : ℝ)^6359
        have hw : |(1062194017/2000000000 : ℝ)|=(1062194017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349565113/2500000000 : ℝ)|^8407 ≤ (44261144808967/100000000000000 : ℝ)^6359
        have hw : |(1349565113/2500000000 : ℝ)|=(1349565113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064608691/10000000000 : ℝ)|^8407 ≤ (12421447062141/100000000000000 : ℝ)^6359
        have hw : |(-2064608691/10000000000 : ℝ)|=(2064608691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s4_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177141023/5000000000 : ℝ)*x 0 + (224762137/500000000 : ℝ)*x 1 + (1054418631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177141023/5000000000 : ℝ)^8407 ≤ (33313852710459/100000000000000 : ℝ)^6359 := by
    have hnat : (2177141023 : ℕ)^8407*100000000000000^6359 ≤ 33313852710459^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177141023 5000000000 33313852710459 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224762137/500000000 : ℝ)^8407 ≤ (3474703166123/10000000000000 : ℝ)^6359 := by
    have hnat : (224762137 : ℕ)^8407*10000000000000^6359 ≤ 3474703166123^6359*500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224762137 500000000 3474703166123 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054418631/2500000000 : ℝ)^8407 ≤ (3193911561971/10000000000000 : ℝ)^6359 := by
    have hnat : (1054418631 : ℕ)^8407*10000000000000^6359 ≤ 3193911561971^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054418631 2500000000 3193911561971 10000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177141023/5000000000 : ℝ), (224762137/500000000 : ℝ), (1054418631/2500000000 : ℝ)] ![(33313852710459/100000000000000 : ℝ), (3474703166123/10000000000000 : ℝ), (3193911561971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177141023/5000000000 : ℝ)|^8407 ≤ (33313852710459/100000000000000 : ℝ)^6359
        have hw : |(2177141023/5000000000 : ℝ)|=(2177141023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224762137/500000000 : ℝ)|^8407 ≤ (3474703166123/10000000000000 : ℝ)^6359
        have hw : |(224762137/500000000 : ℝ)|=(224762137/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054418631/2500000000 : ℝ)|^8407 ≤ (3193911561971/10000000000000 : ℝ)^6359
        have hw : |(1054418631/2500000000 : ℝ)|=(1054418631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2261/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5419/50000 : ℝ) ^ (4203/1024 : ℝ) ≤ (5469231624396799/50000000000000000000 : ℝ) := by
    have hpowers : (5419/50000 : ℝ)^4203 ≤ (5469231624396799/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5419 : ℕ)^4203*50000000000000000000^1024 ≤ 5469231624396799^1024*50000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5419 50000 5469231624396799 50000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5419/50000 : ℝ)) (X := (5469231624396799/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14727/100000 : ℝ) ^ (4203/1024 : ℝ) ≤ (19253141102279271/50000000000000000000 : ℝ) := by
    have hpowers : (14727/100000 : ℝ)^4203 ≤ (19253141102279271/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14727 : ℕ)^4203*50000000000000000000^1024 ≤ 19253141102279271^1024*100000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14727 100000 19253141102279271 50000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14727/100000 : ℝ)) (X := (19253141102279271/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005469231624396799/25000000000000000000 : ℝ) ≤ (10000532955497299/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25005469231624396799/25000000000000000000 : ℝ)^1024 ≤ (10000532955497299/10000000000000000 : ℝ)^4203 := by
      have hnat : (25005469231624396799 : ℕ)^1024*10000000000000000^4203 ≤ 10000532955497299^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005469231624396799 25000000000000000000 10000532955497299 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000532955497299/10000000000000000 : ℝ)) (X := (25005469231624396799/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002472237272667607/5000000000000000000 : ℝ) ≤ (2500301106081677/2500000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (5002472237272667607/5000000000000000000 : ℝ)^1024 ≤ (2500301106081677/2500000000000000 : ℝ)^4203 := by
      have hnat : (5002472237272667607 : ℕ)^1024*2500000000000000^4203 ≤ 2500301106081677^4203*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002472237272667607 5000000000000000000 2500301106081677 2500000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500301106081677/2500000000000000 : ℝ)) (X := (5002472237272667607/5000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019253141102279271/25000000000000000000 : ℝ) ≤ (10001875893156117/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25019253141102279271/25000000000000000000 : ℝ)^1024 ≤ (10001875893156117/10000000000000000 : ℝ)^4203 := by
      have hnat : (25019253141102279271 : ℕ)^1024*10000000000000000^4203 ≤ 10001875893156117^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019253141102279271 25000000000000000000 10001875893156117 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001875893156117/10000000000000000 : ℝ)) (X := (25019253141102279271/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5469231624396799/50000000000000000000 : ℝ) ≤ ((38877517905582726327/38890000000000000000 : ℝ)+2*(671468829409/388900000000000 : ℝ)*(5419/50000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (38877517905582726327/38890000000000000000 : ℝ)+2*(671468829409/388900000000000 : ℝ)*(5419/50000 : ℝ)=(10000532955497299/10000000000000000 : ℝ) by norm_num, show 1+2*(5469231624396799/50000000000000000000 : ℝ)=(25005469231624396799/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19253141102279271/50000000000000000000 : ℝ)+(5469231624396799/50000000000000000000 : ℝ) ≤ ((38877517905582726327/38890000000000000000 : ℝ)+(671468829409/388900000000000 : ℝ)*((14727/100000 : ℝ)+(5419/50000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (38877517905582726327/38890000000000000000 : ℝ)+(671468829409/388900000000000 : ℝ)*((14727/100000 : ℝ)+(5419/50000 : ℝ))=(2500301106081677/2500000000000000 : ℝ) by norm_num, show 1+(19253141102279271/50000000000000000000 : ℝ)+(5469231624396799/50000000000000000000 : ℝ)=(5002472237272667607/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19253141102279271/50000000000000000000 : ℝ) ≤ ((38877517905582726327/38890000000000000000 : ℝ)+2*(671468829409/388900000000000 : ℝ)*(14727/100000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (38877517905582726327/38890000000000000000 : ℝ)+2*(671468829409/388900000000000 : ℝ)*(14727/100000 : ℝ)=(10001875893156117/10000000000000000 : ℝ) by norm_num, show 1+2*(19253141102279271/50000000000000000000 : ℝ)=(25019253141102279271/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38877517905582726327/38890000000000000000 : ℝ)*(X 1 0+X 2 0)+(671468829409/388900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (5419/50000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (38877517905582726327/38890000000000000000 : ℝ)) (alpha := (671468829409/388900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38877517905582726327/38890000000000000000 : ℝ)*(X 0 1+X 2 1)+(671468829409/388900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (5419/50000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (38877517905582726327/38890000000000000000 : ℝ)) (alpha := (671468829409/388900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38877517905582726327/38890000000000000000 : ℝ)*(X 0 2+X 1 2)+(671468829409/388900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (5419/50000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (38877517905582726327/38890000000000000000 : ℝ)) (alpha := (671468829409/388900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066155149/5000000000 : ℝ)*X 0 0+(1079729507/2000000000 : ℝ)*X 0 1+(5260301603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346200777/10000000000 : ℝ)*X 1 0+(-550641779/2500000000 : ℝ)*X 1 1+(263015073/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673100111/5000000000 : ℝ)*X 2 0+(1315075371/2500000000 : ℝ)*X 2 1+(-2202567821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870853637/2000000000 : ℝ)*X 0 0+(4216893703/10000000000 : ℝ)*X 0 1+(4496021371/10000000000 : ℝ)*X 0 2+(870853637/2000000000 : ℝ)*X 1 0+(4216893703/10000000000 : ℝ)*X 1 1+(4496021371/10000000000 : ℝ)*X 1 2+(870853637/2000000000 : ℝ)*X 2 0+(4216893703/10000000000 : ℝ)*X 2 1+(4496021371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132316679/10000000000 : ℝ)*X 0 0+(1315171939/2500000000 : ℝ)*X 0 1+(337391241/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310970053/10000000000 : ℝ)*X 1 0+(-2064609203/10000000000 : ℝ)*X 1 1+(5398260109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062194017/2000000000 : ℝ)*X 2 0+(1349565113/2500000000 : ℝ)*X 2 1+(-2064608691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177141023/5000000000 : ℝ)*X 0 0+(224762137/500000000 : ℝ)*X 0 1+(1054418631/2500000000 : ℝ)*X 0 2+(2177141023/5000000000 : ℝ)*X 1 0+(224762137/500000000 : ℝ)*X 1 1+(1054418631/2500000000 : ℝ)*X 1 2+(2177141023/5000000000 : ℝ)*X 2 0+(224762137/500000000 : ℝ)*X 2 1+(1054418631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5191589759118279365258552919/972250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (430677359/25000000000000 : ℝ)*(base19) + (436976229/25000000000000 : ℝ)*(base23) + (116932101/25000000000000 : ℝ)*(upper2) + (14998207/10000000000000 : ℝ)*(upper3) + (5405503695870101/100000000000000 : ℝ)*(major0) + (5405503695870101/100000000000000 : ℝ)*(major1) + (5405503695870101/100000000000000 : ℝ)*(major2) + (7228325928256133/100000000000000 : ℝ)*(sp0) + (3614182513463283/50000000000000 : ℝ)*(sp1) + (1807087483477637/25000000000000 : ℝ)*(sp2) + (55978403150999/1562500000000 : ℝ)*(sp3) + (40821379869/100000000000000 : ℝ)*(sp4) + (15067820539/100000000000000 : ℝ)*(sp6) + (1133122399/5000000000000 : ℝ)*(sp7) + (895660116027979/25000000000000 : ℝ)*(f.failure) + (3614183374818001/50000000000000 : ℝ)*(f.sum) + (7732886470833/9722500000000000000000000000 : ℝ)*base66 + (4670127288352749027/3889000000000000000000000000000000 : ℝ)*base67 + (29344931938184749027/3889000000000000000000000000000000 : ℝ)*base69 + (20478684023497749027/3889000000000000000000000000000000 : ℝ)*base71 + (20838543053331/19445000000000000000000000000 : ℝ)*base74 + (22815820909151749027/3889000000000000000000000000000000 : ℝ)*base75 + (48665472768976749027/3889000000000000000000000000000000 : ℝ)*base77 + (41773908083396250973/3889000000000000000000000000000000 : ℝ)*base80 + (57353676456073/9722500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (29231/62500000000000000000 : ℝ)*base90 + (29231/62500000000000000000 : ℝ)*base92 + (29231/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4106670127431703950476606421/972250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253415181/25000000000000 : ℝ)*(base19) + (808328587/50000000000000 : ℝ)*(base23) + (30760729/25000000000000 : ℝ)*(upper2) + (418640477/100000000000000 : ℝ)*(upper3) + (2717906277437759/50000000000000 : ℝ)*(major0) + (2717906277437759/50000000000000 : ℝ)*(major1) + (2717906277437759/50000000000000 : ℝ)*(major2) + (8398273887/50000000000000 : ℝ)*(sp1) + (13234219461/20000000000000 : ℝ)*(sp2) + (1024759899/100000000000000 : ℝ)*(sp3) + (7268896507349493/100000000000000 : ℝ)*(sp4) + (3634439348570497/50000000000000 : ℝ)*(sp5) + (3634414359797507/50000000000000 : ℝ)*(sp6) + (180136371842277/5000000000000 : ℝ)*(sp7) + (3602728461605439/100000000000000 : ℝ)*(f.failure) + (7268896507349493/100000000000000 : ℝ)*(f.sum) + (40512482122651/9722500000000000000000000000 : ℝ)*base65 + (10100201242143781193/1944500000000000000000000000000000 : ℝ)*base67 + (8799316324200218807/1944500000000000000000000000000000 : ℝ)*base70 + (12098062347258781193/1944500000000000000000000000000000 : ℝ)*base71 + (25423277446067/19445000000000000000000000000 : ℝ)*base73 + (7209936168278781193/1944500000000000000000000000000000 : ℝ)*base75 + (14986257714768781193/1944500000000000000000000000000000 : ℝ)*base77 + (11473208090036218807/1944500000000000000000000000000000 : ℝ)*base80 + (17178986134647/4861250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1432171/250000000000000000000 : ℝ)*base90 + (1432171/250000000000000000000 : ℝ)*base92 + (1432171/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1214_s5_0 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132805407/10000000000 : ℝ)*x 0 + (5393087769/10000000000 : ℝ)*x 1 + (164548003/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132805407/10000000000 : ℝ)^8407 ≤ (12966749116763/100000000000000 : ℝ)^6359 := by
    have hnat : (2132805407 : ℕ)^8407*100000000000000^6359 ≤ 12966749116763^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132805407 10000000000 12966749116763 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393087769/10000000000 : ℝ)^8407 ≤ (22102541322159/50000000000000 : ℝ)^6359 := by
    have hnat : (5393087769 : ℕ)^8407*50000000000000^6359 ≤ 22102541322159^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393087769 10000000000 22102541322159 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164548003/312500000 : ℝ)^8407 ≤ (42828168229357/100000000000000 : ℝ)^6359 := by
    have hnat : (164548003 : ℕ)^8407*100000000000000^6359 ≤ 42828168229357^6359*312500000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164548003 312500000 42828168229357 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132805407/10000000000 : ℝ), (5393087769/10000000000 : ℝ), (164548003/312500000 : ℝ)] ![(12966749116763/100000000000000 : ℝ), (22102541322159/50000000000000 : ℝ), (42828168229357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132805407/10000000000 : ℝ)|^8407 ≤ (12966749116763/100000000000000 : ℝ)^6359
        have hw : |(-2132805407/10000000000 : ℝ)|=(2132805407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393087769/10000000000 : ℝ)|^8407 ≤ (22102541322159/50000000000000 : ℝ)^6359
        have hw : |(5393087769/10000000000 : ℝ)|=(5393087769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164548003/312500000 : ℝ)|^8407 ≤ (42828168229357/100000000000000 : ℝ)^6359
        have hw : |(164548003/312500000 : ℝ)|=(164548003/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_1 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672398453/5000000000 : ℝ)*x 0 + (-1098751631/5000000000 : ℝ)*x 1 + (1053107219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672398453/5000000000 : ℝ)^8407 ≤ (21841268658897/50000000000000 : ℝ)^6359 := by
    have hnat : (2672398453 : ℕ)^8407*50000000000000^6359 ≤ 21841268658897^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672398453 5000000000 21841268658897 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098751631/5000000000 : ℝ)^8407 ≤ (3372323614607/25000000000000 : ℝ)^6359 := by
    have hnat : (1098751631 : ℕ)^8407*25000000000000^6359 ≤ 3372323614607^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098751631 5000000000 3372323614607 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053107219/2000000000 : ℝ)^8407 ≤ (10707042054651/25000000000000 : ℝ)^6359 := by
    have hnat : (1053107219 : ℕ)^8407*25000000000000^6359 ≤ 10707042054651^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053107219 2000000000 10707042054651 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672398453/5000000000 : ℝ), (-1098751631/5000000000 : ℝ), (1053107219/2000000000 : ℝ)] ![(21841268658897/50000000000000 : ℝ), (3372323614607/25000000000000 : ℝ), (10707042054651/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672398453/5000000000 : ℝ)|^8407 ≤ (21841268658897/50000000000000 : ℝ)^6359
        have hw : |(2672398453/5000000000 : ℝ)|=(2672398453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098751631/5000000000 : ℝ)|^8407 ≤ (3372323614607/25000000000000 : ℝ)^6359
        have hw : |(-1098751631/5000000000 : ℝ)|=(1098751631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053107219/2000000000 : ℝ)|^8407 ≤ (10707042054651/25000000000000 : ℝ)^6359
        have hw : |(1053107219/2000000000 : ℝ)|=(1053107219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_2 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344796907/10000000000 : ℝ)*x 0 + (5265536099/10000000000 : ℝ)*x 1 + (-439500651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344796907/10000000000 : ℝ)^8407 ≤ (43682537328599/100000000000000 : ℝ)^6359 := by
    have hnat : (5344796907 : ℕ)^8407*100000000000000^6359 ≤ 43682537328599^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344796907 10000000000 43682537328599 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265536099/10000000000 : ℝ)^8407 ≤ (42828168261617/100000000000000 : ℝ)^6359 := by
    have hnat : (5265536099 : ℕ)^8407*100000000000000^6359 ≤ 42828168261617^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265536099 10000000000 42828168261617 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439500651/2000000000 : ℝ)^8407 ≤ (674464720081/5000000000000 : ℝ)^6359 := by
    have hnat : (439500651 : ℕ)^8407*5000000000000^6359 ≤ 674464720081^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439500651 2000000000 674464720081 5000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344796907/10000000000 : ℝ), (5265536099/10000000000 : ℝ), (-439500651/2000000000 : ℝ)] ![(43682537328599/100000000000000 : ℝ), (42828168261617/100000000000000 : ℝ), (674464720081/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344796907/10000000000 : ℝ)|^8407 ≤ (43682537328599/100000000000000 : ℝ)^6359
        have hw : |(5344796907/10000000000 : ℝ)|=(5344796907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265536099/10000000000 : ℝ)|^8407 ≤ (42828168261617/100000000000000 : ℝ)^6359
        have hw : |(5265536099/10000000000 : ℝ)|=(5265536099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439500651/2000000000 : ℝ)|^8407 ≤ (674464720081/5000000000000 : ℝ)^6359
        have hw : |(-439500651/2000000000 : ℝ)|=(439500651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_3 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354559559/10000000000 : ℝ)*x 0 + (1056936297/2500000000 : ℝ)*x 1 + (4485094523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354559559/10000000000 : ℝ)^8407 ≤ (33316659748617/100000000000000 : ℝ)^6359 := by
    have hnat : (4354559559 : ℕ)^8407*100000000000000^6359 ≤ 33316659748617^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354559559 10000000000 33316659748617 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056936297/2500000000 : ℝ)^8407 ≤ (32039977489983/100000000000000 : ℝ)^6359 := by
    have hnat : (1056936297 : ℕ)^8407*100000000000000^6359 ≤ 32039977489983^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056936297 2500000000 32039977489983 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485094523/10000000000 : ℝ)^8407 ≤ (1385734509993/4000000000000 : ℝ)^6359 := by
    have hnat : (4485094523 : ℕ)^8407*4000000000000^6359 ≤ 1385734509993^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485094523 10000000000 1385734509993 4000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354559559/10000000000 : ℝ), (1056936297/2500000000 : ℝ), (4485094523/10000000000 : ℝ)] ![(33316659748617/100000000000000 : ℝ), (32039977489983/100000000000000 : ℝ), (1385734509993/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354559559/10000000000 : ℝ)|^8407 ≤ (33316659748617/100000000000000 : ℝ)^6359
        have hw : |(4354559559/10000000000 : ℝ)|=(4354559559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056936297/2500000000 : ℝ)|^8407 ≤ (32039977489983/100000000000000 : ℝ)^6359
        have hw : |(1056936297/2500000000 : ℝ)|=(1056936297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485094523/10000000000 : ℝ)|^8407 ≤ (1385734509993/4000000000000 : ℝ)^6359
        have hw : |(4485094523/10000000000 : ℝ)|=(4485094523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_4 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066405207/5000000000 : ℝ)*x 0 + (658233031/1250000000 : ℝ)*x 1 + (337047401/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066405207/5000000000 : ℝ)^8407 ≤ (12966789361571/100000000000000 : ℝ)^6359 := by
    have hnat : (1066405207 : ℕ)^8407*100000000000000^6359 ≤ 12966789361571^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066405207 5000000000 12966789361571 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658233031/1250000000 : ℝ)^8407 ≤ (42831696960269/100000000000000 : ℝ)^6359 := by
    have hnat : (658233031 : ℕ)^8407*100000000000000^6359 ≤ 42831696960269^6359*1250000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658233031 1250000000 42831696960269 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337047401/625000000 : ℝ)^8407 ≤ (44201513662843/100000000000000 : ℝ)^6359 := by
    have hnat : (337047401 : ℕ)^8407*100000000000000^6359 ≤ 44201513662843^6359*625000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337047401 625000000 44201513662843 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066405207/5000000000 : ℝ), (658233031/1250000000 : ℝ), (337047401/625000000 : ℝ)] ![(12966789361571/100000000000000 : ℝ), (42831696960269/100000000000000 : ℝ), (44201513662843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066405207/5000000000 : ℝ)|^8407 ≤ (12966789361571/100000000000000 : ℝ)^6359
        have hw : |(-1066405207/5000000000 : ℝ)|=(1066405207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658233031/1250000000 : ℝ)|^8407 ≤ (42831696960269/100000000000000 : ℝ)^6359
        have hw : |(658233031/1250000000 : ℝ)|=(658233031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337047401/625000000 : ℝ)|^8407 ≤ (44201513662843/100000000000000 : ℝ)^6359
        have hw : |(337047401/625000000 : ℝ)|=(337047401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_5 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062462841/2000000000 : ℝ)*x 0 + (-82811237/400000000 : ℝ)*x 1 + (1348189601/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062462841/2000000000 : ℝ)^8407 ≤ (216659511909/500000000000 : ℝ)^6359 := by
    have hnat : (1062462841 : ℕ)^8407*500000000000^6359 ≤ 216659511909^6359*2000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062462841 2000000000 216659511909 500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82811237/400000000 : ℝ)^8407 ≤ (6233292035643/50000000000000 : ℝ)^6359 := by
    have hnat : (82811237 : ℕ)^8407*50000000000000^6359 ≤ 6233292035643^6359*400000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82811237 400000000 6233292035643 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348189601/2500000000 : ℝ)^8407 ≤ (5525189191601/12500000000000 : ℝ)^6359 := by
    have hnat : (1348189601 : ℕ)^8407*12500000000000^6359 ≤ 5525189191601^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348189601 2500000000 5525189191601 12500000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062462841/2000000000 : ℝ), (-82811237/400000000 : ℝ), (1348189601/2500000000 : ℝ)] ![(216659511909/500000000000 : ℝ), (6233292035643/50000000000000 : ℝ), (5525189191601/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062462841/2000000000 : ℝ)|^8407 ≤ (216659511909/500000000000 : ℝ)^6359
        have hw : |(1062462841/2000000000 : ℝ)|=(1062462841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-82811237/400000000 : ℝ)|^8407 ≤ (6233292035643/50000000000000 : ℝ)^6359
        have hw : |(-82811237/400000000 : ℝ)|=(82811237/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348189601/2500000000 : ℝ)|^8407 ≤ (5525189191601/12500000000000 : ℝ)^6359
        have hw : |(1348189601/2500000000 : ℝ)|=(1348189601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_6 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312314181/10000000000 : ℝ)*x 0 + (2696379217/5000000000 : ℝ)*x 1 + (-517570229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312314181/10000000000 : ℝ)^8407 ≤ (21665951061493/50000000000000 : ℝ)^6359 := by
    have hnat : (5312314181 : ℕ)^8407*50000000000000^6359 ≤ 21665951061493^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312314181 10000000000 21665951061493 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696379217/5000000000 : ℝ)^8407 ≤ (8840302771579/20000000000000 : ℝ)^6359 := by
    have hnat : (2696379217 : ℕ)^8407*20000000000000^6359 ≤ 8840302771579^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696379217 5000000000 8840302771579 20000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517570229/2500000000 : ℝ)^8407 ≤ (3116645999909/25000000000000 : ℝ)^6359 := by
    have hnat : (517570229 : ℕ)^8407*25000000000000^6359 ≤ 3116645999909^6359*2500000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517570229 2500000000 3116645999909 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312314181/10000000000 : ℝ), (2696379217/5000000000 : ℝ), (-517570229/2500000000 : ℝ)] ![(21665951061493/50000000000000 : ℝ), (8840302771579/20000000000000 : ℝ), (3116645999909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312314181/10000000000 : ℝ)|^8407 ≤ (21665951061493/50000000000000 : ℝ)^6359
        have hw : |(5312314181/10000000000 : ℝ)|=(5312314181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696379217/5000000000 : ℝ)|^8407 ≤ (8840302771579/20000000000000 : ℝ)^6359
        have hw : |(2696379217/5000000000 : ℝ)|=(2696379217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517570229/2500000000 : ℝ)|^8407 ≤ (3116645999909/25000000000000 : ℝ)^6359
        have hw : |(-517570229/2500000000 : ℝ)|=(517570229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1214_s5_7 (p : ℝ) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354569687/10000000000 : ℝ)*x 0 + (2242216257/5000000000 : ℝ)*x 1 + (4228409659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354569687/10000000000 : ℝ)^8407 ≤ (16658381097107/50000000000000 : ℝ)^6359 := by
    have hnat : (4354569687 : ℕ)^8407*50000000000000^6359 ≤ 16658381097107^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354569687 10000000000 16658381097107 50000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242216257/5000000000 : ℝ)^8407 ≤ (34636602632487/100000000000000 : ℝ)^6359 := by
    have hnat : (2242216257 : ℕ)^8407*100000000000000^6359 ≤ 34636602632487^6359*5000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242216257 5000000000 34636602632487 100000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228409659/10000000000 : ℝ)^8407 ≤ (8011658791447/25000000000000 : ℝ)^6359 := by
    have hnat : (4228409659 : ℕ)^8407*25000000000000^6359 ≤ 8011658791447^6359*10000000000^8407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228409659 10000000000 8011658791447 25000000000000 8407 6359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8407/2048 : ℝ)) 8407 6359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354569687/10000000000 : ℝ), (2242216257/5000000000 : ℝ), (4228409659/10000000000 : ℝ)] ![(16658381097107/50000000000000 : ℝ), (34636602632487/100000000000000 : ℝ), (8011658791447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354569687/10000000000 : ℝ)|^8407 ≤ (16658381097107/50000000000000 : ℝ)^6359
        have hw : |(4354569687/10000000000 : ℝ)|=(4354569687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242216257/5000000000 : ℝ)|^8407 ≤ (34636602632487/100000000000000 : ℝ)^6359
        have hw : |(2242216257/5000000000 : ℝ)|=(2242216257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228409659/10000000000 : ℝ)|^8407 ≤ (8011658791447/25000000000000 : ℝ)^6359
        have hw : |(4228409659/10000000000 : ℝ)|=(4228409659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1214_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11417/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2261/20000 : ℝ) ^ (4203/1024 : ℝ) ≤ (81289874789527/625000000000000000 : ℝ) := by
    have hpowers : (2261/20000 : ℝ)^4203 ≤ (81289874789527/625000000000000000 : ℝ)^1024 := by
      have hnat : (2261 : ℕ)^4203*625000000000000000^1024 ≤ 81289874789527^1024*20000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 20000 81289874789527 625000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/20000 : ℝ)) (X := (81289874789527/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4203/1024 : ℝ) ≤ (16746820309218947/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4203 ≤ (16746820309218947/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4203*50000000000000000000^1024 ≤ 16746820309218947^1024*20000^4203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 16746820309218947 50000000000000000000 4203 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (16746820309218947/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (312581289874789527/312500000000000000 : ℝ) ≤ (1000063370083587/1000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (312581289874789527/312500000000000000 : ℝ)^1024 ≤ (1000063370083587/1000000000000000 : ℝ)^4203 := by
      have hnat : (312581289874789527 : ℕ)^1024*1000000000000000^4203 ≤ 1000063370083587^4203*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312581289874789527 312500000000000000 1000063370083587 1000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000063370083587/1000000000000000 : ℝ)) (X := (312581289874789527/312500000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023250010292381107/50000000000000000000 : ℝ) ≤ (10001132706396637/10000000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (50023250010292381107/50000000000000000000 : ℝ)^1024 ≤ (10001132706396637/10000000000000000 : ℝ)^4203 := by
      have hnat : (50023250010292381107 : ℕ)^1024*10000000000000000^4203 ≤ 10001132706396637^4203*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023250010292381107 50000000000000000000 10001132706396637 10000000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001132706396637/10000000000000000 : ℝ)) (X := (50023250010292381107/50000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016746820309218947/25000000000000000000 : ℝ) ≤ (2500407927989351/2500000000000000 : ℝ) ^ (4203/1024 : ℝ) := by
    have hpowers : (25016746820309218947/25000000000000000000 : ℝ)^1024 ≤ (2500407927989351/2500000000000000 : ℝ)^4203 := by
      have hnat : (25016746820309218947 : ℕ)^1024*2500000000000000^4203 ≤ 2500407927989351^4203*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016746820309218947 25000000000000000000 2500407927989351 2500000000000000 1024 4203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500407927989351/2500000000000000 : ℝ)) (X := (25016746820309218947/25000000000000000000 : ℝ)) (by norm_num) 4203 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(81289874789527/625000000000000000 : ℝ) ≤ ((2929057422772015723/2930000000000000000 : ℝ)+2*(499005560767/293000000000000 : ℝ)*(2261/20000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (2929057422772015723/2930000000000000000 : ℝ)+2*(499005560767/293000000000000 : ℝ)*(2261/20000 : ℝ)=(1000063370083587/1000000000000000 : ℝ) by norm_num, show 1+2*(81289874789527/625000000000000000 : ℝ)=(312581289874789527/312500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16746820309218947/50000000000000000000 : ℝ)+(81289874789527/625000000000000000 : ℝ) ≤ ((2929057422772015723/2930000000000000000 : ℝ)+(499005560767/293000000000000 : ℝ)*((2847/20000 : ℝ)+(2261/20000 : ℝ)))^(4203/1024 : ℝ) := by
    rw [show (2929057422772015723/2930000000000000000 : ℝ)+(499005560767/293000000000000 : ℝ)*((2847/20000 : ℝ)+(2261/20000 : ℝ))=(10001132706396637/10000000000000000 : ℝ) by norm_num, show 1+(16746820309218947/50000000000000000000 : ℝ)+(81289874789527/625000000000000000 : ℝ)=(50023250010292381107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16746820309218947/50000000000000000000 : ℝ) ≤ ((2929057422772015723/2930000000000000000 : ℝ)+2*(499005560767/293000000000000 : ℝ)*(2847/20000 : ℝ))^(4203/1024 : ℝ) := by
    rw [show (2929057422772015723/2930000000000000000 : ℝ)+2*(499005560767/293000000000000 : ℝ)*(2847/20000 : ℝ)=(2500407927989351/2500000000000000 : ℝ) by norm_num, show 1+2*(16746820309218947/50000000000000000000 : ℝ)=(25016746820309218947/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2929057422772015723/2930000000000000000 : ℝ)*(X 1 0+X 2 0)+(499005560767/293000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2929057422772015723/2930000000000000000 : ℝ)) (alpha := (499005560767/293000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2929057422772015723/2930000000000000000 : ℝ)*(X 0 1+X 2 1)+(499005560767/293000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2929057422772015723/2930000000000000000 : ℝ)) (alpha := (499005560767/293000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2929057422772015723/2930000000000000000 : ℝ)*(X 0 2+X 1 2)+(499005560767/293000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4203/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (2929057422772015723/2930000000000000000 : ℝ)) (alpha := (499005560767/293000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132805407/10000000000 : ℝ)*X 0 0+(5393087769/10000000000 : ℝ)*X 0 1+(164548003/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672398453/5000000000 : ℝ)*X 1 0+(-1098751631/5000000000 : ℝ)*X 1 1+(1053107219/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344796907/10000000000 : ℝ)*X 2 0+(5265536099/10000000000 : ℝ)*X 2 1+(-439500651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354559559/10000000000 : ℝ)*X 0 0+(1056936297/2500000000 : ℝ)*X 0 1+(4485094523/10000000000 : ℝ)*X 0 2+(4354559559/10000000000 : ℝ)*X 1 0+(1056936297/2500000000 : ℝ)*X 1 1+(4485094523/10000000000 : ℝ)*X 1 2+(4354559559/10000000000 : ℝ)*X 2 0+(1056936297/2500000000 : ℝ)*X 2 1+(4485094523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1066405207/5000000000 : ℝ)*X 0 0+(658233031/1250000000 : ℝ)*X 0 1+(337047401/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062462841/2000000000 : ℝ)*X 1 0+(-82811237/400000000 : ℝ)*X 1 1+(1348189601/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312314181/10000000000 : ℝ)*X 2 0+(2696379217/5000000000 : ℝ)*X 2 1+(-517570229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354569687/10000000000 : ℝ)*X 0 0+(2242216257/5000000000 : ℝ)*X 0 1+(4228409659/10000000000 : ℝ)*X 0 2+(4354569687/10000000000 : ℝ)*X 1 0+(2242216257/5000000000 : ℝ)*X 1 1+(4228409659/10000000000 : ℝ)*X 1 2+(4354569687/10000000000 : ℝ)*X 2 0+(2242216257/5000000000 : ℝ)*X 2 1+(4228409659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1214_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40414656080703394889109/14650000000000000000000000000 : ℝ) := by norm_num
    linear_combination (537005269/100000000000000 : ℝ)*(base19) + (15957959/3125000000000 : ℝ)*(base23) + (14867849/100000000000000 : ℝ)*(lower2) + (58034089/100000000000000 : ℝ)*(upper3) + (24375677/50000000000000 : ℝ)*(upper5) + (5862886968475959/100000000000000 : ℝ)*(major0) + (5862886968475959/100000000000000 : ℝ)*(major1) + (5862886968475959/100000000000000 : ℝ)*(major2) + (783997516553063/10000000000000 : ℝ)*(sp0) + (7839989989439911/100000000000000 : ℝ)*(sp1) + (1959997503947623/25000000000000 : ℝ)*(sp2) + (485721979146587/12500000000000 : ℝ)*(sp3) + (15360914549/100000000000000 : ℝ)*(sp4) + (1497075609/20000000000000 : ℝ)*(sp7) + (194289165927537/5000000000000 : ℝ)*(f.failure) + (391999526322259/5000000000000 : ℝ)*(f.sum) + (9988876504603/14650000000000000000000000000 : ℝ)*base65 + (2208907548901033357/293000000000000000000000000000000 : ℝ)*base67 + (1900049714709966643/293000000000000000000000000000000 : ℝ)*base70 + (1487281439616033357/293000000000000000000000000000000 : ℝ)*base71 + (49984693035847/14650000000000000000000000000 : ℝ)*base74 + (2301129410242966643/293000000000000000000000000000000 : ℝ)*base76 + (369224826362033357/293000000000000000000000000000000 : ℝ)*base77 + (4951122342296966643/293000000000000000000000000000000 : ℝ)*base80 + (32814554723397/14650000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (108093/12500000000000000000 : ℝ)*base90 + (108093/12500000000000000000 : ℝ)*base92 + (108093/12500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4980122061200161256079/457812500000000000000000000 : ℝ) := by norm_num
    linear_combination (1975184873/100000000000000 : ℝ)*(base19) + (1064335369/50000000000000 : ℝ)*(base23) + (217271511/100000000000000 : ℝ)*(upper3) + (3306291/4000000000000 : ℝ)*(lower4) + (155631/78125000000 : ℝ)*(upper5) + (1473310075740481/25000000000000 : ℝ)*(major0) + (1473310075740481/25000000000000 : ℝ)*(major1) + (1473310075740481/25000000000000 : ℝ)*(major2) + (26854063089/50000000000000 : ℝ)*(sp1) + (7398206243/12500000000000 : ℝ)*(sp2) + (3940289724988213/50000000000000 : ℝ)*(sp4) + (63044190133323/800000000000 : ℝ)*(sp5) + (123133095869621/1562500000000 : ℝ)*(sp6) + (1952950396672333/50000000000000 : ℝ)*(sp7) + (1952950396672333/50000000000000 : ℝ)*(f.failure) + (3940289724988213/50000000000000 : ℝ)*(f.sum) + (2166610659751/1831250000000000000000000000 : ℝ)*base65 + (344020058339852763/73250000000000000000000000000000 : ℝ)*base67 + (580727653268647237/73250000000000000000000000000000 : ℝ)*base70 + (416807945112602763/73250000000000000000000000000000 : ℝ)*base71 + (39751057037629/7325000000000000000000000000 : ℝ)*base73 + (1961296421229147237/73250000000000000000000000000000 : ℝ)*base76 + (436213940963352763/73250000000000000000000000000000 : ℝ)*base77 + (122557221978147237/73250000000000000000000000000000 : ℝ)*base80 + (24217320861/114453125000000000000000000 : ℝ)*base81 + (1528337/125000000000000000000 : ℝ)*base90 + (1528337/125000000000000000000 : ℝ)*base92 + (1528337/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1214_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1214_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1214_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1214_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1214_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1214_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4203/1024 : ℝ) ≤ p) (hpb : p ≤ (8407/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3772011/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16297/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1173/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1214_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
