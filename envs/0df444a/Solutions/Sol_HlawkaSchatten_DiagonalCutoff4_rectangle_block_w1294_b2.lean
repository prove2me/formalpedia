-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:04.396993+00:00
-- url     : https://prove2.me/submissions/f8769a6f-8166-49a3-b31f-7cca423c0649

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
theorem support_rectangle_w1294_s6_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086166603/10000000000 : ℝ)*x 0 + (1083043839/2000000000 : ℝ)*x 1 + (524297993/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086166603/10000000000 : ℝ)^2127 ≤ (6346490828947/50000000000000 : ℝ)^1615 := by
    have hnat : (2086166603 : ℕ)^2127*50000000000000^1615 ≤ 6346490828947^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086166603 10000000000 6346490828947 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083043839/2000000000 : ℝ)^2127 ≤ (557281871889/1250000000000 : ℝ)^1615 := by
    have hnat : (1083043839 : ℕ)^2127*1250000000000^1615 ≤ 557281871889^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083043839 2000000000 557281871889 1250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524297993/1000000000 : ℝ)^2127 ≤ (8544893715849/20000000000000 : ℝ)^1615 := by
    have hnat : (524297993 : ℕ)^2127*20000000000000^1615 ≤ 8544893715849^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524297993 1000000000 8544893715849 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086166603/10000000000 : ℝ), (1083043839/2000000000 : ℝ), (524297993/1000000000 : ℝ)] ![(6346490828947/50000000000000 : ℝ), (557281871889/1250000000000 : ℝ), (8544893715849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086166603/10000000000 : ℝ)|^2127 ≤ (6346490828947/50000000000000 : ℝ)^1615
        have hw : |(-2086166603/10000000000 : ℝ)|=(2086166603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083043839/2000000000 : ℝ)|^2127 ≤ (557281871889/1250000000000 : ℝ)^1615
        have hw : |(1083043839/2000000000 : ℝ)|=(1083043839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524297993/1000000000 : ℝ)|^2127 ≤ (8544893715849/20000000000000 : ℝ)^1615
        have hw : |(524297993/1000000000 : ℝ)|=(524297993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349778573/10000000000 : ℝ)*x 0 + (-2173964887/10000000000 : ℝ)*x 1 + (1310744983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349778573/10000000000 : ℝ)^2127 ≤ (5484293658541/12500000000000 : ℝ)^1615 := by
    have hnat : (5349778573 : ℕ)^2127*12500000000000^1615 ≤ 5484293658541^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349778573 10000000000 5484293658541 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173964887/10000000000 : ℝ)^2127 ≤ (13401182116629/100000000000000 : ℝ)^1615 := by
    have hnat : (2173964887 : ℕ)^2127*100000000000000^1615 ≤ 13401182116629^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173964887 10000000000 13401182116629 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310744983/2500000000 : ℝ)^2127 ≤ (4272446860071/10000000000000 : ℝ)^1615 := by
    have hnat : (1310744983 : ℕ)^2127*10000000000000^1615 ≤ 4272446860071^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310744983 2500000000 4272446860071 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349778573/10000000000 : ℝ), (-2173964887/10000000000 : ℝ), (1310744983/2500000000 : ℝ)] ![(5484293658541/12500000000000 : ℝ), (13401182116629/100000000000000 : ℝ), (4272446860071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349778573/10000000000 : ℝ)|^2127 ≤ (5484293658541/12500000000000 : ℝ)^1615
        have hw : |(5349778573/10000000000 : ℝ)|=(5349778573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173964887/10000000000 : ℝ)|^2127 ≤ (13401182116629/100000000000000 : ℝ)^1615
        have hw : |(-2173964887/10000000000 : ℝ)|=(2173964887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310744983/2500000000 : ℝ)|^2127 ≤ (4272446860071/10000000000000 : ℝ)^1615
        have hw : |(1310744983/2500000000 : ℝ)|=(1310744983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213991143/400000000 : ℝ)*x 0 + (5242979929/10000000000 : ℝ)*x 1 + (-2173964889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213991143/400000000 : ℝ)^2127 ≤ (43874349289931/100000000000000 : ℝ)^1615 := by
    have hnat : (213991143 : ℕ)^2127*100000000000000^1615 ≤ 43874349289931^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213991143 400000000 43874349289931 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242979929/10000000000 : ℝ)^2127 ≤ (42724468568513/100000000000000 : ℝ)^1615 := by
    have hnat : (5242979929 : ℕ)^2127*100000000000000^1615 ≤ 42724468568513^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242979929 10000000000 42724468568513 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173964889/10000000000 : ℝ)^2127 ≤ (13401182132867/100000000000000 : ℝ)^1615 := by
    have hnat : (2173964889 : ℕ)^2127*100000000000000^1615 ≤ 13401182132867^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173964889 10000000000 13401182132867 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213991143/400000000 : ℝ), (5242979929/10000000000 : ℝ), (-2173964889/10000000000 : ℝ)] ![(43874349289931/100000000000000 : ℝ), (42724468568513/100000000000000 : ℝ), (13401182132867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213991143/400000000 : ℝ)|^2127 ≤ (43874349289931/100000000000000 : ℝ)^1615
        have hw : |(213991143/400000000 : ℝ)|=(213991143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242979929/10000000000 : ℝ)|^2127 ≤ (42724468568513/100000000000000 : ℝ)^1615
        have hw : |(5242979929/10000000000 : ℝ)|=(5242979929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173964889/10000000000 : ℝ)|^2127 ≤ (13401182132867/100000000000000 : ℝ)^1615
        have hw : |(-2173964889/10000000000 : ℝ)|=(2173964889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1084831073/2500000000 : ℝ)*x 0 + (2082822707/5000000000 : ℝ)*x 1 + (564988563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084831073/2500000000 : ℝ)^2127 ≤ (6660468958429/20000000000000 : ℝ)^1615 := by
    have hnat : (1084831073 : ℕ)^2127*20000000000000^1615 ≤ 6660468958429^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084831073 2500000000 6660468958429 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082822707/5000000000 : ℝ)^2127 ≤ (1262324416203/4000000000000 : ℝ)^1615 := by
    have hnat : (2082822707 : ℕ)^2127*4000000000000^1615 ≤ 1262324416203^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082822707 5000000000 1262324416203 4000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564988563/1250000000 : ℝ)^2127 ≤ (1756977239259/5000000000000 : ℝ)^1615 := by
    have hnat : (564988563 : ℕ)^2127*5000000000000^1615 ≤ 1756977239259^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564988563 1250000000 1756977239259 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084831073/2500000000 : ℝ), (2082822707/5000000000 : ℝ), (564988563/1250000000 : ℝ)] ![(6660468958429/20000000000000 : ℝ), (1262324416203/4000000000000 : ℝ), (1756977239259/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084831073/2500000000 : ℝ)|^2127 ≤ (6660468958429/20000000000000 : ℝ)^1615
        have hw : |(1084831073/2500000000 : ℝ)|=(1084831073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082822707/5000000000 : ℝ)|^2127 ≤ (1262324416203/4000000000000 : ℝ)^1615
        have hw : |(2082822707/5000000000 : ℝ)|=(2082822707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564988563/1250000000 : ℝ)|^2127 ≤ (1756977239259/5000000000000 : ℝ)^1615
        have hw : |(564988563/1250000000 : ℝ)|=(564988563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-4074569/19531250 : ℝ)*x 0 + (2621797263/5000000000 : ℝ)*x 1 + (2707300719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4074569/19531250 : ℝ)^2127 ≤ (6346541813409/50000000000000 : ℝ)^1615 := by
    have hnat : (4074569 : ℕ)^2127*50000000000000^1615 ≤ 6346541813409^1615*19531250^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4074569 19531250 6346541813409 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621797263/5000000000 : ℝ)^2127 ≤ (21365532370039/50000000000000 : ℝ)^1615 := by
    have hnat : (2621797263 : ℕ)^2127*50000000000000^1615 ≤ 21365532370039^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621797263 5000000000 21365532370039 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707300719/5000000000 : ℝ)^2127 ≤ (11143962904991/25000000000000 : ℝ)^1615 := by
    have hnat : (2707300719 : ℕ)^2127*25000000000000^1615 ≤ 11143962904991^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707300719 5000000000 11143962904991 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4074569/19531250 : ℝ), (2621797263/5000000000 : ℝ), (2707300719/5000000000 : ℝ)] ![(6346541813409/50000000000000 : ℝ), (21365532370039/50000000000000 : ℝ), (11143962904991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4074569/19531250 : ℝ)|^2127 ≤ (6346541813409/50000000000000 : ℝ)^1615
        have hw : |(-4074569/19531250 : ℝ)|=(4074569/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621797263/5000000000 : ℝ)|^2127 ≤ (21365532370039/50000000000000 : ℝ)^1615
        have hw : |(2621797263/5000000000 : ℝ)|=(2621797263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707300719/5000000000 : ℝ)|^2127 ≤ (11143962904991/25000000000000 : ℝ)^1615
        have hw : |(2707300719/5000000000 : ℝ)|=(2707300719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305669693/10000000000 : ℝ)*x 0 + (-2002343381/10000000000 : ℝ)*x 1 + (1353650359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305669693/10000000000 : ℝ)^2127 ≤ (8679709328671/20000000000000 : ℝ)^1615 := by
    have hnat : (5305669693 : ℕ)^2127*20000000000000^1615 ≤ 8679709328671^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305669693 10000000000 8679709328671 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002343381/10000000000 : ℝ)^2127 ≤ (2405120349203/20000000000000 : ℝ)^1615 := by
    have hnat : (2002343381 : ℕ)^2127*20000000000000^1615 ≤ 2405120349203^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002343381 10000000000 2405120349203 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353650359/2500000000 : ℝ)^2127 ≤ (44575851598279/100000000000000 : ℝ)^1615 := by
    have hnat : (1353650359 : ℕ)^2127*100000000000000^1615 ≤ 44575851598279^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353650359 2500000000 44575851598279 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305669693/10000000000 : ℝ), (-2002343381/10000000000 : ℝ), (1353650359/2500000000 : ℝ)] ![(8679709328671/20000000000000 : ℝ), (2405120349203/20000000000000 : ℝ), (44575851598279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305669693/10000000000 : ℝ)|^2127 ≤ (8679709328671/20000000000000 : ℝ)^1615
        have hw : |(5305669693/10000000000 : ℝ)|=(5305669693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002343381/10000000000 : ℝ)|^2127 ≤ (2405120349203/20000000000000 : ℝ)^1615
        have hw : |(-2002343381/10000000000 : ℝ)|=(2002343381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353650359/2500000000 : ℝ)|^2127 ≤ (44575851598279/100000000000000 : ℝ)^1615
        have hw : |(1353650359/2500000000 : ℝ)|=(1353650359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652834847/5000000000 : ℝ)*x 0 + (5414601433/10000000000 : ℝ)*x 1 + (-2002343383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652834847/5000000000 : ℝ)^2127 ≤ (2712409165883/6250000000000 : ℝ)^1615 := by
    have hnat : (2652834847 : ℕ)^2127*6250000000000^1615 ≤ 2712409165883^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652834847 5000000000 2712409165883 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414601433/10000000000 : ℝ)^2127 ≤ (44575851565751/100000000000000 : ℝ)^1615 := by
    have hnat : (5414601433 : ℕ)^2127*100000000000000^1615 ≤ 44575851565751^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414601433 10000000000 44575851565751 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002343383/10000000000 : ℝ)^2127 ≤ (6012800880917/50000000000000 : ℝ)^1615 := by
    have hnat : (2002343383 : ℕ)^2127*50000000000000^1615 ≤ 6012800880917^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002343383 10000000000 6012800880917 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652834847/5000000000 : ℝ), (5414601433/10000000000 : ℝ), (-2002343383/10000000000 : ℝ)] ![(2712409165883/6250000000000 : ℝ), (44575851565751/100000000000000 : ℝ), (6012800880917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652834847/5000000000 : ℝ)|^2127 ≤ (2712409165883/6250000000000 : ℝ)^1615
        have hw : |(2652834847/5000000000 : ℝ)|=(2652834847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414601433/10000000000 : ℝ)|^2127 ≤ (44575851565751/100000000000000 : ℝ)^1615
        have hw : |(5414601433/10000000000 : ℝ)|=(5414601433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002343383/10000000000 : ℝ)|^2127 ≤ (6012800880917/50000000000000 : ℝ)^1615
        have hw : |(-2002343383/10000000000 : ℝ)|=(2002343383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s6_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4339350469/10000000000 : ℝ)*x 0 + (564830549/1250000000 : ℝ)*x 1 + (2083458013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339350469/10000000000 : ℝ)^2127 ≤ (33302609378813/100000000000000 : ℝ)^1615 := by
    have hnat : (4339350469 : ℕ)^2127*100000000000000^1615 ≤ 33302609378813^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339350469 10000000000 33302609378813 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564830549/1250000000 : ℝ)^2127 ≤ (8781650499949/25000000000000 : ℝ)^1615 := by
    have hnat : (564830549 : ℕ)^2127*25000000000000^1615 ≤ 8781650499949^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564830549 1250000000 8781650499949 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083458013/5000000000 : ℝ)^2127 ≤ (1973174287827/6250000000000 : ℝ)^1615 := by
    have hnat : (2083458013 : ℕ)^2127*6250000000000^1615 ≤ 1973174287827^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083458013 5000000000 1973174287827 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339350469/10000000000 : ℝ), (564830549/1250000000 : ℝ), (2083458013/5000000000 : ℝ)] ![(33302609378813/100000000000000 : ℝ), (8781650499949/25000000000000 : ℝ), (1973174287827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339350469/10000000000 : ℝ)|^2127 ≤ (33302609378813/100000000000000 : ℝ)^1615
        have hw : |(4339350469/10000000000 : ℝ)|=(4339350469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564830549/1250000000 : ℝ)|^2127 ≤ (8781650499949/25000000000000 : ℝ)^1615
        have hw : |(564830549/1250000000 : ℝ)|=(564830549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083458013/5000000000 : ℝ)|^2127 ≤ (1973174287827/6250000000000 : ℝ)^1615
        have hw : |(2083458013/5000000000 : ℝ)|=(2083458013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11031/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3669/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (551/5000 : ℝ) ^ (4253/1024 : ℝ) ≤ (1314568961366079/12500000000000000000 : ℝ) := by
    have hpowers : (551/5000 : ℝ)^4253 ≤ (1314568961366079/12500000000000000000 : ℝ)^1024 := by
      have hnat : (551 : ℕ)^4253*12500000000000000000^1024 ≤ 1314568961366079^1024*5000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        551 5000 1314568961366079 12500000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (551/5000 : ℝ)) (X := (1314568961366079/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (4253/1024 : ℝ) ≤ (17341997331611663/50000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^4253 ≤ (17341997331611663/50000000000000000000 : ℝ)^1024 := by
      have hnat : (459 : ℕ)^4253*50000000000000000000^1024 ≤ 17341997331611663^1024*3125^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 17341997331611663 50000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (17341997331611663/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251314568961366079/6250000000000000000 : ℝ) ≤ (10000506376167139/10000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (6251314568961366079/6250000000000000000 : ℝ)^1024 ≤ (10000506376167139/10000000000000000 : ℝ)^4253 := by
      have hnat : (6251314568961366079 : ℕ)^1024*10000000000000000^4253 ≤ 10000506376167139^4253*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251314568961366079 6250000000000000000 10000506376167139 10000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000506376167139/10000000000000000 : ℝ)) (X := (6251314568961366079/6250000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022600273177075979/50000000000000000000 : ℝ) ≤ (5000544056190561/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50022600273177075979/50000000000000000000 : ℝ)^1024 ≤ (5000544056190561/5000000000000000 : ℝ)^4253 := by
      have hnat : (50022600273177075979 : ℕ)^1024*5000000000000000^4253 ≤ 5000544056190561^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022600273177075979 50000000000000000000 5000544056190561 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000544056190561/5000000000000000 : ℝ)) (X := (50022600273177075979/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017341997331611663/25000000000000000000 : ℝ) ≤ (2000333969719021/2000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (25017341997331611663/25000000000000000000 : ℝ)^1024 ≤ (2000333969719021/2000000000000000 : ℝ)^4253 := by
      have hnat : (25017341997331611663 : ℕ)^1024*2000000000000000^4253 ≤ 2000333969719021^4253*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017341997331611663 25000000000000000000 2000333969719021 2000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000333969719021/2000000000000000 : ℝ)) (X := (25017341997331611663/25000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1314568961366079/12500000000000000000 : ℝ) ≤ ((9167258980406220133/9170000000000000000 : ℝ)+2*(581736213983/366800000000000 : ℝ)*(551/5000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (9167258980406220133/9170000000000000000 : ℝ)+2*(581736213983/366800000000000 : ℝ)*(551/5000 : ℝ)=(10000506376167139/10000000000000000 : ℝ) by norm_num, show 1+2*(1314568961366079/12500000000000000000 : ℝ)=(6251314568961366079/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17341997331611663/50000000000000000000 : ℝ)+(1314568961366079/12500000000000000000 : ℝ) ≤ ((9167258980406220133/9170000000000000000 : ℝ)+(581736213983/366800000000000 : ℝ)*((459/3125 : ℝ)+(551/5000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (9167258980406220133/9170000000000000000 : ℝ)+(581736213983/366800000000000 : ℝ)*((459/3125 : ℝ)+(551/5000 : ℝ))=(5000544056190561/5000000000000000 : ℝ) by norm_num, show 1+(17341997331611663/50000000000000000000 : ℝ)+(1314568961366079/12500000000000000000 : ℝ)=(50022600273177075979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17341997331611663/50000000000000000000 : ℝ) ≤ ((9167258980406220133/9170000000000000000 : ℝ)+2*(581736213983/366800000000000 : ℝ)*(459/3125 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (9167258980406220133/9170000000000000000 : ℝ)+2*(581736213983/366800000000000 : ℝ)*(459/3125 : ℝ)=(2000333969719021/2000000000000000 : ℝ) by norm_num, show 1+2*(17341997331611663/50000000000000000000 : ℝ)=(25017341997331611663/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9167258980406220133/9170000000000000000 : ℝ)*(X 1 0+X 2 0)+(581736213983/366800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (9167258980406220133/9170000000000000000 : ℝ)) (alpha := (581736213983/366800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9167258980406220133/9170000000000000000 : ℝ)*(X 0 1+X 2 1)+(581736213983/366800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (9167258980406220133/9170000000000000000 : ℝ)) (alpha := (581736213983/366800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9167258980406220133/9170000000000000000 : ℝ)*(X 0 2+X 1 2)+(581736213983/366800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (9167258980406220133/9170000000000000000 : ℝ)) (alpha := (581736213983/366800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086166603/10000000000 : ℝ)*X 0 0+(1083043839/2000000000 : ℝ)*X 0 1+(524297993/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349778573/10000000000 : ℝ)*X 1 0+(-2173964887/10000000000 : ℝ)*X 1 1+(1310744983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213991143/400000000 : ℝ)*X 2 0+(5242979929/10000000000 : ℝ)*X 2 1+(-2173964889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084831073/2500000000 : ℝ)*X 0 0+(2082822707/5000000000 : ℝ)*X 0 1+(564988563/1250000000 : ℝ)*X 0 2+(1084831073/2500000000 : ℝ)*X 1 0+(2082822707/5000000000 : ℝ)*X 1 1+(564988563/1250000000 : ℝ)*X 1 2+(1084831073/2500000000 : ℝ)*X 2 0+(2082822707/5000000000 : ℝ)*X 2 1+(564988563/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4074569/19531250 : ℝ)*X 0 0+(2621797263/5000000000 : ℝ)*X 0 1+(2707300719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305669693/10000000000 : ℝ)*X 1 0+(-2002343381/10000000000 : ℝ)*X 1 1+(1353650359/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652834847/5000000000 : ℝ)*X 2 0+(5414601433/10000000000 : ℝ)*X 2 1+(-2002343383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339350469/10000000000 : ℝ)*X 0 0+(564830549/1250000000 : ℝ)*X 0 1+(2083458013/5000000000 : ℝ)*X 0 2+(4339350469/10000000000 : ℝ)*X 1 0+(564830549/1250000000 : ℝ)*X 1 1+(2083458013/5000000000 : ℝ)*X 1 2+(4339350469/10000000000 : ℝ)*X 2 0+(564830549/1250000000 : ℝ)*X 2 1+(2083458013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23326724225699090178317109/6550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (680117117/100000000000000 : ℝ)*(base19) + (19868301/3125000000000 : ℝ)*(base23) + (24877543/100000000000000 : ℝ)*(lower2) + (11325663/12500000000000 : ℝ)*(upper3) + (6799991/12500000000000 : ℝ)*(upper5) + (431433986178321/10000000000000 : ℝ)*(major0) + (431433986178321/10000000000000 : ℝ)*(major1) + (431433986178321/10000000000000 : ℝ)*(major2) + (2902945696664627/50000000000000 : ℝ)*(sp0) + (36286902206563/625000000000 : ℝ)*(sp1) + (1161180879476313/20000000000000 : ℝ)*(sp2) + (1411383676588967/50000000000000 : ℝ)*(sp3) + (6819918971/50000000000000 : ℝ)*(sp4) + (721851021/10000000000000 : ℝ)*(sp7) + (176423410730509/6250000000000 : ℝ)*(f.failure) + (5805905033167197/100000000000000 : ℝ)*(f.sum) + (702580245689/262000000000000000000000000 : ℝ)*base65 + (174866230504473099/13100000000000000000000000000000 : ℝ)*base67 + (56786288983073099/13100000000000000000000000000000 : ℝ)*base69 + (129801915580473099/13100000000000000000000000000000 : ℝ)*base71 + (274837466783/262000000000000000000000000 : ℝ)*base74 + (148657090136673099/13100000000000000000000000000000 : ℝ)*base75 + (33424769721973099/13100000000000000000000000000000 : ℝ)*base77 + (357801535999173099/13100000000000000000000000000000 : ℝ)*base79 + (1158902807967/262000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6927927/625000000000000000000 : ℝ)*base90 + (6927927/625000000000000000000 : ℝ)*base92 + (6927927/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3064811808110006895469159767/458500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2968061/250000000000 : ℝ)*(base19) + (1292472697/100000000000000 : ℝ)*(base23) + (134640549/100000000000000 : ℝ)*(upper3) + (23882917/50000000000000 : ℝ)*(lower4) + (137989391/100000000000000 : ℝ)*(upper5) + (4345409484506567/100000000000000 : ℝ)*(major0) + (4345409484506567/100000000000000 : ℝ)*(major1) + (4345409484506567/100000000000000 : ℝ)*(major2) + (23807017449/100000000000000 : ℝ)*(sp1) + (25505238341/100000000000000 : ℝ)*(sp2) + (1461929006526661/25000000000000 : ℝ)*(sp4) + (5847691031864797/100000000000000 : ℝ)*(sp5) + (2923844614197803/50000000000000 : ℝ)*(sp6) + (1421551360046051/50000000000000 : ℝ)*(sp7) + (1421551360046051/50000000000000 : ℝ)*(f.failure) + (1461929006526661/25000000000000 : ℝ)*(f.sum) + (74258267987679/18340000000000000000000000000 : ℝ)*base66 + (12189715155669138411/917000000000000000000000000000000 : ℝ)*base67 + (4756918473337138411/917000000000000000000000000000000 : ℝ)*base69 + (5531759823566861589/917000000000000000000000000000000 : ℝ)*base72 + (141365488752601/18340000000000000000000000000 : ℝ)*base73 + (1965725799958861589/917000000000000000000000000000000 : ℝ)*base76 + (2232028891836138411/917000000000000000000000000000000 : ℝ)*base77 + (5594531539438138411/917000000000000000000000000000000 : ℝ)*base79 + (5083488981339/18340000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (23122247/5000000000000000000000 : ℝ)*base89 + (23122247/5000000000000000000000 : ℝ)*base91 + (23122247/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1294_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1294_s7_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1043089769/5000000000 : ℝ)*x 0 + (5415115459/10000000000 : ℝ)*x 1 + (209723003/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043089769/5000000000 : ℝ)^2127 ≤ (12693085309607/100000000000000 : ℝ)^1615 := by
    have hnat : (1043089769 : ℕ)^2127*100000000000000^1615 ≤ 12693085309607^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043089769 5000000000 12693085309607 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415115459/10000000000 : ℝ)^2127 ≤ (1783256998387/4000000000000 : ℝ)^1615 := by
    have hnat : (5415115459 : ℕ)^2127*4000000000000^1615 ≤ 1783256998387^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415115459 10000000000 1783256998387 4000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209723003/400000000 : ℝ)^2127 ≤ (8545097941671/20000000000000 : ℝ)^1615 := by
    have hnat : (209723003 : ℕ)^2127*20000000000000^1615 ≤ 8545097941671^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209723003 400000000 8545097941671 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1043089769/5000000000 : ℝ), (5415115459/10000000000 : ℝ), (209723003/400000000 : ℝ)] ![(12693085309607/100000000000000 : ℝ), (1783256998387/4000000000000 : ℝ), (8545097941671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1043089769/5000000000 : ℝ)|^2127 ≤ (12693085309607/100000000000000 : ℝ)^1615
        have hw : |(-1043089769/5000000000 : ℝ)|=(1043089769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415115459/10000000000 : ℝ)|^2127 ≤ (1783256998387/4000000000000 : ℝ)^1615
        have hw : |(5415115459/10000000000 : ℝ)|=(5415115459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209723003/400000000 : ℝ)|^2127 ≤ (8545097941671/20000000000000 : ℝ)^1615
        have hw : |(209723003/400000000 : ℝ)|=(209723003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069950113/2000000000 : ℝ)*x 0 + (-2173874053/10000000000 : ℝ)*x 1 + (163846151/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069950113/2000000000 : ℝ)^2127 ≤ (43874046750077/100000000000000 : ℝ)^1615 := by
    have hnat : (1069950113 : ℕ)^2127*100000000000000^1615 ≤ 43874046750077^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069950113 2000000000 43874046750077 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173874053/10000000000 : ℝ)^2127 ≤ (107203557353/800000000000 : ℝ)^1615 := by
    have hnat : (2173874053 : ℕ)^2127*800000000000^1615 ≤ 107203557353^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173874053 10000000000 107203557353 800000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163846151/312500000 : ℝ)^2127 ≤ (5340688570643/12500000000000 : ℝ)^1615 := by
    have hnat : (163846151 : ℕ)^2127*12500000000000^1615 ≤ 5340688570643^1615*312500000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163846151 312500000 5340688570643 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069950113/2000000000 : ℝ), (-2173874053/10000000000 : ℝ), (163846151/312500000 : ℝ)] ![(43874046750077/100000000000000 : ℝ), (107203557353/800000000000 : ℝ), (5340688570643/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069950113/2000000000 : ℝ)|^2127 ≤ (43874046750077/100000000000000 : ℝ)^1615
        have hw : |(1069950113/2000000000 : ℝ)|=(1069950113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173874053/10000000000 : ℝ)|^2127 ≤ (107203557353/800000000000 : ℝ)^1615
        have hw : |(-2173874053/10000000000 : ℝ)|=(2173874053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163846151/312500000 : ℝ)|^2127 ≤ (5340688570643/12500000000000 : ℝ)^1615
        have hw : |(163846151/312500000 : ℝ)|=(163846151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534975157/1000000000 : ℝ)*x 0 + (209722969/400000000 : ℝ)*x 1 + (-1086938081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534975157/1000000000 : ℝ)^2127 ≤ (43874057605211/100000000000000 : ℝ)^1615 := by
    have hnat : (534975157 : ℕ)^2127*100000000000000^1615 ≤ 43874057605211^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534975157 1000000000 43874057605211 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209722969/400000000 : ℝ)^2127 ≤ (8545096117167/20000000000000 : ℝ)^1615 := by
    have hnat : (209722969 : ℕ)^2127*20000000000000^1615 ≤ 8545096117167^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209722969 400000000 8545096117167 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086938081/5000000000 : ℝ)^2127 ≤ (6700230895601/50000000000000 : ℝ)^1615 := by
    have hnat : (1086938081 : ℕ)^2127*50000000000000^1615 ≤ 6700230895601^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086938081 5000000000 6700230895601 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534975157/1000000000 : ℝ), (209722969/400000000 : ℝ), (-1086938081/5000000000 : ℝ)] ![(43874057605211/100000000000000 : ℝ), (8545096117167/20000000000000 : ℝ), (6700230895601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534975157/1000000000 : ℝ)|^2127 ≤ (43874057605211/100000000000000 : ℝ)^1615
        have hw : |(534975157/1000000000 : ℝ)|=(534975157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209722969/400000000 : ℝ)|^2127 ≤ (8545096117167/20000000000000 : ℝ)^1615
        have hw : |(209722969/400000000 : ℝ)|=(209722969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086938081/5000000000 : ℝ)|^2127 ≤ (6700230895601/50000000000000 : ℝ)^1615
        have hw : |(-1086938081/5000000000 : ℝ)|=(1086938081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1084832421/2500000000 : ℝ)*x 0 + (4165851407/10000000000 : ℝ)*x 1 + (4519702447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084832421/2500000000 : ℝ)^2127 ≤ (260174994471/781250000000 : ℝ)^1615 := by
    have hnat : (1084832421 : ℕ)^2127*781250000000^1615 ≤ 260174994471^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084832421 2500000000 260174994471 781250000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4165851407/10000000000 : ℝ)^2127 ≤ (31560165725423/100000000000000 : ℝ)^1615 := by
    have hnat : (4165851407 : ℕ)^2127*100000000000000^1615 ≤ 31560165725423^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165851407 10000000000 31560165725423 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519702447/10000000000 : ℝ)^2127 ≤ (1756871748191/5000000000000 : ℝ)^1615 := by
    have hnat : (4519702447 : ℕ)^2127*5000000000000^1615 ≤ 1756871748191^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519702447 10000000000 1756871748191 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084832421/2500000000 : ℝ), (4165851407/10000000000 : ℝ), (4519702447/10000000000 : ℝ)] ![(260174994471/781250000000 : ℝ), (31560165725423/100000000000000 : ℝ), (1756871748191/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084832421/2500000000 : ℝ)|^2127 ≤ (260174994471/781250000000 : ℝ)^1615
        have hw : |(1084832421/2500000000 : ℝ)|=(1084832421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4165851407/10000000000 : ℝ)|^2127 ≤ (31560165725423/100000000000000 : ℝ)^1615
        have hw : |(4165851407/10000000000 : ℝ)|=(4165851407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519702447/10000000000 : ℝ)|^2127 ≤ (1756871748191/5000000000000 : ℝ)^1615
        have hw : |(4519702447/10000000000 : ℝ)|=(4519702447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086192257/10000000000 : ℝ)*x 0 + (1048737707/2000000000 : ℝ)*x 1 + (216579953/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086192257/10000000000 : ℝ)^2127 ≤ (3173296807663/25000000000000 : ℝ)^1615 := by
    have hnat : (2086192257 : ℕ)^2127*25000000000000^1615 ≤ 3173296807663^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086192257 10000000000 3173296807663 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048737707/2000000000 : ℝ)^2127 ≤ (42732073714701/100000000000000 : ℝ)^1615 := by
    have hnat : (1048737707 : ℕ)^2127*100000000000000^1615 ≤ 42732073714701^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048737707 2000000000 42732073714701 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216579953/400000000 : ℝ)^2127 ≤ (1392960595163/3125000000000 : ℝ)^1615 := by
    have hnat : (216579953 : ℕ)^2127*3125000000000^1615 ≤ 1392960595163^1615*400000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216579953 400000000 1392960595163 3125000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086192257/10000000000 : ℝ), (1048737707/2000000000 : ℝ), (216579953/400000000 : ℝ)] ![(3173296807663/25000000000000 : ℝ), (42732073714701/100000000000000 : ℝ), (1392960595163/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086192257/10000000000 : ℝ)|^2127 ≤ (3173296807663/25000000000000 : ℝ)^1615
        have hw : |(-2086192257/10000000000 : ℝ)|=(2086192257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048737707/2000000000 : ℝ)|^2127 ≤ (42732073714701/100000000000000 : ℝ)^1615
        have hw : |(1048737707/2000000000 : ℝ)|=(1048737707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216579953/400000000 : ℝ)|^2127 ≤ (1392960595163/3125000000000 : ℝ)^1615
        have hw : |(216579953/400000000 : ℝ)|=(216579953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (41450737/78125000 : ℝ)*x 0 + (-1001225359/5000000000 : ℝ)*x 1 + (2707249323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41450737/78125000 : ℝ)^2127 ≤ (21699406059241/50000000000000 : ℝ)^1615 := by
    have hnat : (41450737 : ℕ)^2127*50000000000000^1615 ≤ 21699406059241^1615*78125000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41450737 78125000 21699406059241 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001225359/5000000000 : ℝ)^2127 ≤ (12026450762977/100000000000000 : ℝ)^1615 := by
    have hnat : (1001225359 : ℕ)^2127*100000000000000^1615 ≤ 12026450762977^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001225359 5000000000 12026450762977 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707249323/5000000000 : ℝ)^2127 ≤ (22287368552213/50000000000000 : ℝ)^1615 := by
    have hnat : (2707249323 : ℕ)^2127*50000000000000^1615 ≤ 22287368552213^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707249323 5000000000 22287368552213 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41450737/78125000 : ℝ), (-1001225359/5000000000 : ℝ), (2707249323/5000000000 : ℝ)] ![(21699406059241/50000000000000 : ℝ), (12026450762977/100000000000000 : ℝ), (22287368552213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41450737/78125000 : ℝ)|^2127 ≤ (21699406059241/50000000000000 : ℝ)^1615
        have hw : |(41450737/78125000 : ℝ)|=(41450737/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001225359/5000000000 : ℝ)|^2127 ≤ (12026450762977/100000000000000 : ℝ)^1615
        have hw : |(-1001225359/5000000000 : ℝ)|=(1001225359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707249323/5000000000 : ℝ)|^2127 ≤ (22287368552213/50000000000000 : ℝ)^1615
        have hw : |(2707249323/5000000000 : ℝ)|=(2707249323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305694247/10000000000 : ℝ)*x 0 + (2707249381/5000000000 : ℝ)*x 1 + (-2002450681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305694247/10000000000 : ℝ)^2127 ≤ (21699405579849/50000000000000 : ℝ)^1615 := by
    have hnat : (5305694247 : ℕ)^2127*50000000000000^1615 ≤ 21699405579849^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305694247 10000000000 21699405579849 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707249381/5000000000 : ℝ)^2127 ≤ (8914947672429/20000000000000 : ℝ)^1615 := by
    have hnat : (2707249381 : ℕ)^2127*20000000000000^1615 ≤ 8914947672429^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707249381 5000000000 8914947672429 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002450681/10000000000 : ℝ)^2127 ≤ (12026450470311/100000000000000 : ℝ)^1615 := by
    have hnat : (2002450681 : ℕ)^2127*100000000000000^1615 ≤ 12026450470311^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002450681 10000000000 12026450470311 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305694247/10000000000 : ℝ), (2707249381/5000000000 : ℝ), (-2002450681/10000000000 : ℝ)] ![(21699405579849/50000000000000 : ℝ), (8914947672429/20000000000000 : ℝ), (12026450470311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305694247/10000000000 : ℝ)|^2127 ≤ (21699405579849/50000000000000 : ℝ)^1615
        have hw : |(5305694247/10000000000 : ℝ)|=(5305694247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707249381/5000000000 : ℝ)|^2127 ≤ (8914947672429/20000000000000 : ℝ)^1615
        have hw : |(2707249381/5000000000 : ℝ)|=(2707249381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002450681/10000000000 : ℝ)|^2127 ≤ (12026450470311/100000000000000 : ℝ)^1615
        have hw : |(-2002450681/10000000000 : ℝ)|=(2002450681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s7_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (433935733/1000000000 : ℝ)*x 0 + (2259220759/5000000000 : ℝ)*x 1 + (4167117227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433935733/1000000000 : ℝ)^2127 ≤ (16651339363573/50000000000000 : ℝ)^1615 := by
    have hnat : (433935733 : ℕ)^2127*50000000000000^1615 ≤ 16651339363573^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433935733 1000000000 16651339363573 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259220759/5000000000 : ℝ)^2127 ≤ (17562262476599/50000000000000 : ℝ)^1615 := by
    have hnat : (2259220759 : ℕ)^2127*50000000000000^1615 ≤ 17562262476599^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259220759 5000000000 17562262476599 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167117227/10000000000 : ℝ)^2127 ≤ (31572796306549/100000000000000 : ℝ)^1615 := by
    have hnat : (4167117227 : ℕ)^2127*100000000000000^1615 ≤ 31572796306549^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167117227 10000000000 31572796306549 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433935733/1000000000 : ℝ), (2259220759/5000000000 : ℝ), (4167117227/10000000000 : ℝ)] ![(16651339363573/50000000000000 : ℝ), (17562262476599/50000000000000 : ℝ), (31572796306549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433935733/1000000000 : ℝ)|^2127 ≤ (16651339363573/50000000000000 : ℝ)^1615
        have hw : |(433935733/1000000000 : ℝ)|=(433935733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259220759/5000000000 : ℝ)|^2127 ≤ (17562262476599/50000000000000 : ℝ)^1615
        have hw : |(2259220759/5000000000 : ℝ)|=(2259220759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167117227/10000000000 : ℝ)|^2127 ≤ (31572796306549/100000000000000 : ℝ)^1615
        have hw : |(4167117227/10000000000 : ℝ)|=(4167117227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7337/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (11031/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (5280109846459191/50000000000000000000 : ℝ) := by
    have hpowers : (11031/100000 : ℝ)^4253 ≤ (5280109846459191/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11031 : ℕ)^4253*50000000000000000000^1024 ≤ 5280109846459191^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11031 100000 5280109846459191 50000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11031/100000 : ℝ)) (X := (5280109846459191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3669/25000 : ℝ) ^ (4253/1024 : ℝ) ≤ (8641613802715721/25000000000000000000 : ℝ) := by
    have hpowers : (3669/25000 : ℝ)^4253 ≤ (8641613802715721/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3669 : ℕ)^4253*25000000000000000000^1024 ≤ 8641613802715721^1024*25000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3669 25000 8641613802715721 25000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3669/25000 : ℝ)) (X := (8641613802715721/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005280109846459191/25000000000000000000 : ℝ) ≤ (2000101695726067/2000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (25005280109846459191/25000000000000000000 : ℝ)^1024 ≤ (2000101695726067/2000000000000000 : ℝ)^4253 := by
      have hnat : (25005280109846459191 : ℕ)^1024*2000000000000000^4253 ≤ 2000101695726067^4253*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005280109846459191 25000000000000000000 2000101695726067 2000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101695726067/2000000000000000 : ℝ)) (X := (25005280109846459191/25000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022563337451890633/50000000000000000000 : ℝ) ≤ (625067895898677/625000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50022563337451890633/50000000000000000000 : ℝ)^1024 ≤ (625067895898677/625000000000000 : ℝ)^4253 := by
      have hnat : (50022563337451890633 : ℕ)^1024*625000000000000^4253 ≤ 625067895898677^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022563337451890633 50000000000000000000 625067895898677 625000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625067895898677/625000000000000 : ℝ)) (X := (50022563337451890633/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508641613802715721/12500000000000000000 : ℝ) ≤ (10001664190127329/10000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (12508641613802715721/12500000000000000000 : ℝ)^1024 ≤ (10001664190127329/10000000000000000 : ℝ)^4253 := by
      have hnat : (12508641613802715721 : ℕ)^1024*10000000000000000^4253 ≤ 10001664190127329^4253*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508641613802715721 12500000000000000000 10001664190127329 10000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001664190127329/10000000000000000 : ℝ)) (X := (12508641613802715721/12500000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5280109846459191/50000000000000000000 : ℝ) ≤ ((12146368250361410087/12150000000000000000 : ℝ)+2*(577855748497/364500000000000 : ℝ)*(11031/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (12146368250361410087/12150000000000000000 : ℝ)+2*(577855748497/364500000000000 : ℝ)*(11031/100000 : ℝ)=(2000101695726067/2000000000000000 : ℝ) by norm_num, show 1+2*(5280109846459191/50000000000000000000 : ℝ)=(25005280109846459191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8641613802715721/25000000000000000000 : ℝ)+(5280109846459191/50000000000000000000 : ℝ) ≤ ((12146368250361410087/12150000000000000000 : ℝ)+(577855748497/364500000000000 : ℝ)*((3669/25000 : ℝ)+(11031/100000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (12146368250361410087/12150000000000000000 : ℝ)+(577855748497/364500000000000 : ℝ)*((3669/25000 : ℝ)+(11031/100000 : ℝ))=(625067895898677/625000000000000 : ℝ) by norm_num, show 1+(8641613802715721/25000000000000000000 : ℝ)+(5280109846459191/50000000000000000000 : ℝ)=(50022563337451890633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8641613802715721/25000000000000000000 : ℝ) ≤ ((12146368250361410087/12150000000000000000 : ℝ)+2*(577855748497/364500000000000 : ℝ)*(3669/25000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (12146368250361410087/12150000000000000000 : ℝ)+2*(577855748497/364500000000000 : ℝ)*(3669/25000 : ℝ)=(10001664190127329/10000000000000000 : ℝ) by norm_num, show 1+2*(8641613802715721/25000000000000000000 : ℝ)=(12508641613802715721/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12146368250361410087/12150000000000000000 : ℝ)*(X 1 0+X 2 0)+(577855748497/364500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (12146368250361410087/12150000000000000000 : ℝ)) (alpha := (577855748497/364500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12146368250361410087/12150000000000000000 : ℝ)*(X 0 1+X 2 1)+(577855748497/364500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (12146368250361410087/12150000000000000000 : ℝ)) (alpha := (577855748497/364500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12146368250361410087/12150000000000000000 : ℝ)*(X 0 2+X 1 2)+(577855748497/364500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11031/100000 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (12146368250361410087/12150000000000000000 : ℝ)) (alpha := (577855748497/364500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1043089769/5000000000 : ℝ)*X 0 0+(5415115459/10000000000 : ℝ)*X 0 1+(209723003/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069950113/2000000000 : ℝ)*X 1 0+(-2173874053/10000000000 : ℝ)*X 1 1+(163846151/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534975157/1000000000 : ℝ)*X 2 0+(209722969/400000000 : ℝ)*X 2 1+(-1086938081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084832421/2500000000 : ℝ)*X 0 0+(4165851407/10000000000 : ℝ)*X 0 1+(4519702447/10000000000 : ℝ)*X 0 2+(1084832421/2500000000 : ℝ)*X 1 0+(4165851407/10000000000 : ℝ)*X 1 1+(4519702447/10000000000 : ℝ)*X 1 2+(1084832421/2500000000 : ℝ)*X 2 0+(4165851407/10000000000 : ℝ)*X 2 1+(4519702447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2086192257/10000000000 : ℝ)*X 0 0+(1048737707/2000000000 : ℝ)*X 0 1+(216579953/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41450737/78125000 : ℝ)*X 1 0+(-1001225359/5000000000 : ℝ)*X 1 1+(2707249323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305694247/10000000000 : ℝ)*X 2 0+(2707249381/5000000000 : ℝ)*X 2 1+(-2002450681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433935733/1000000000 : ℝ)*X 0 0+(2259220759/5000000000 : ℝ)*X 0 1+(4167117227/10000000000 : ℝ)*X 0 2+(433935733/1000000000 : ℝ)*X 1 0+(2259220759/5000000000 : ℝ)*X 1 1+(4167117227/10000000000 : ℝ)*X 1 2+(433935733/1000000000 : ℝ)*X 2 0+(2259220759/5000000000 : ℝ)*X 2 1+(4167117227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10922545584668472340077353/3796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241134913/20000000000000 : ℝ)*(base15) + (13967331/4000000000000 : ℝ)*(base29) + (352292241/100000000000000 : ℝ)*(upper2) + (106979139/100000000000000 : ℝ)*(upper4) + (354399217/100000000000000 : ℝ)*(lower5) + (863869263109313/20000000000000 : ℝ)*(major0) + (53991833309123/1250000000000 : ℝ)*(major1) + (53991833309123/1250000000000 : ℝ)*(major2) + (5812630771794357/100000000000000 : ℝ)*(sp0) + (2906320634792083/50000000000000 : ℝ)*(sp1) + (5812581460447001/100000000000000 : ℝ)*(sp2) + (1413025204563503/50000000000000 : ℝ)*(sp3) + (12052647649/100000000000000 : ℝ)*(sp4) + (61014811731/100000000000000 : ℝ)*(sp6) + (1413025204563503/50000000000000 : ℝ)*(f.failure) + (2906321412221003/50000000000000 : ℝ)*(f.sum) + (36856888692071/3645000000000000000000000000 : ℝ)*base65 + (418654623080428897/45562500000000000000000000000000 : ℝ)*base68 + (144335630136553897/45562500000000000000000000000000 : ℝ)*base70 + (7696589063610879307/729000000000000000000000000000000 : ℝ)*base72 + (17059847887897/7290000000000000000000000000 : ℝ)*base73 + (270544147236647647/45562500000000000000000000000000 : ℝ)*base76 + (6823050219716120693/729000000000000000000000000000000 : ℝ)*base77 + (303462957577585147/45562500000000000000000000000000 : ℝ)*base80 + (17306234834047/7290000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10230691/5000000000000000000000 : ℝ)*base89 + (10230691/5000000000000000000000 : ℝ)*base91 + (10230691/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85490125607010069345563201/11250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225265997/12500000000000 : ℝ)*(base19) + (27304039/1562500000000 : ℝ)*(base23) + (266718567/50000000000000 : ℝ)*(lower1) + (7045337/100000000000000 : ℝ)*(upper2) + (94067447/50000000000000 : ℝ)*(upper3) + (103281631/100000000000000 : ℝ)*(upper5) + (2175193065308607/50000000000000 : ℝ)*(major0) + (2175193065308607/50000000000000 : ℝ)*(major1) + (2175193065308607/50000000000000 : ℝ)*(major2) + (1821827683/50000000000000 : ℝ)*(sp2) + (2927206590666077/50000000000000 : ℝ)*(sp4) + (2927205689602089/50000000000000 : ℝ)*(sp5) + (5854407790218293/100000000000000 : ℝ)*(sp6) + (2846358826598189/100000000000000 : ℝ)*(sp7) + (2846358826598189/100000000000000 : ℝ)*(f.failure) + (2927206590666077/50000000000000 : ℝ)*(f.sum) + (1247752541077/337500000000000000000000000 : ℝ)*base65 + (414031191195886799/67500000000000000000000000000000 : ℝ)*base68 + (768652801686613201/67500000000000000000000000000000 : ℝ)*base69 + (24911461499113201/67500000000000000000000000000000 : ℝ)*base71 + (995206962349/168750000000000000000000000 : ℝ)*base74 + (1564877814128386799/67500000000000000000000000000000 : ℝ)*base76 + (612258108353386799/67500000000000000000000000000000 : ℝ)*base78 + (107523156450886799/67500000000000000000000000000000 : ℝ)*base80 + (258408623237/84375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (33758967/10000000000000000000000 : ℝ)*base90 + (33758967/10000000000000000000000 : ℝ)*base92 + (33758967/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1294_s8_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349747487/10000000000 : ℝ)*x 0 + (5243091999/10000000000 : ℝ)*x 1 + (-2173858099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349747487/10000000000 : ℝ)^2127 ≤ (43874013504207/100000000000000 : ℝ)^1615 := by
    have hnat : (5349747487 : ℕ)^2127*100000000000000^1615 ≤ 43874013504207^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349747487 10000000000 43874013504207 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243091999/10000000000 : ℝ)^2127 ≤ (42725671343203/100000000000000 : ℝ)^1615 := by
    have hnat : (5243091999 : ℕ)^2127*100000000000000^1615 ≤ 42725671343203^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243091999 10000000000 42725671343203 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173858099/10000000000 : ℝ)^2127 ≤ (6700157572767/50000000000000 : ℝ)^1615 := by
    have hnat : (2173858099 : ℕ)^2127*50000000000000^1615 ≤ 6700157572767^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173858099 10000000000 6700157572767 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349747487/10000000000 : ℝ), (5243091999/10000000000 : ℝ), (-2173858099/10000000000 : ℝ)] ![(43874013504207/100000000000000 : ℝ), (42725671343203/100000000000000 : ℝ), (6700157572767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349747487/10000000000 : ℝ)|^2127 ≤ (43874013504207/100000000000000 : ℝ)^1615
        have hw : |(5349747487/10000000000 : ℝ)|=(5349747487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243091999/10000000000 : ℝ)|^2127 ≤ (42725671343203/100000000000000 : ℝ)^1615
        have hw : |(5243091999/10000000000 : ℝ)|=(5243091999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173858099/10000000000 : ℝ)|^2127 ≤ (6700157572767/50000000000000 : ℝ)^1615
        have hw : |(-2173858099/10000000000 : ℝ)|=(2173858099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s8_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-417238787/2000000000 : ℝ)*x 0 + (163865779/312500000 : ℝ)*x 1 + (5414481357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417238787/2000000000 : ℝ)^2127 ≤ (12693200676969/100000000000000 : ℝ)^1615 := by
    have hnat : (417238787 : ℕ)^2127*100000000000000^1615 ≤ 12693200676969^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417238787 2000000000 12693200676969 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163865779/312500000 : ℝ)^2127 ≤ (42732249657177/100000000000000 : ℝ)^1615 := by
    have hnat : (163865779 : ℕ)^2127*100000000000000^1615 ≤ 42732249657177^1615*312500000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163865779 312500000 42732249657177 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414481357/10000000000 : ℝ)^2127 ≤ (22287274825117/50000000000000 : ℝ)^1615 := by
    have hnat : (5414481357 : ℕ)^2127*50000000000000^1615 ≤ 22287274825117^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414481357 10000000000 22287274825117 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417238787/2000000000 : ℝ), (163865779/312500000 : ℝ), (5414481357/10000000000 : ℝ)] ![(12693200676969/100000000000000 : ℝ), (42732249657177/100000000000000 : ℝ), (22287274825117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417238787/2000000000 : ℝ)|^2127 ≤ (12693200676969/100000000000000 : ℝ)^1615
        have hw : |(-417238787/2000000000 : ℝ)|=(417238787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163865779/312500000 : ℝ)|^2127 ≤ (42732249657177/100000000000000 : ℝ)^1615
        have hw : |(163865779/312500000 : ℝ)|=(163865779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414481357/10000000000 : ℝ)|^2127 ≤ (22287274825117/50000000000000 : ℝ)^1615
        have hw : |(5414481357/10000000000 : ℝ)|=(5414481357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s8_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305698541/10000000000 : ℝ)*x 0 + (-1955536/9765625 : ℝ)*x 1 + (541448123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305698541/10000000000 : ℝ)^2127 ≤ (21699428709159/50000000000000 : ℝ)^1615 := by
    have hnat : (5305698541 : ℕ)^2127*50000000000000^1615 ≤ 21699428709159^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305698541 10000000000 21699428709159 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955536/9765625 : ℝ)^2127 ≤ (120265942961/1000000000000 : ℝ)^1615 := by
    have hnat : (1955536 : ℕ)^2127*1000000000000^1615 ≤ 120265942961^1615*9765625^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955536 9765625 120265942961 1000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541448123/1000000000 : ℝ)^2127 ≤ (178298193093/400000000000 : ℝ)^1615 := by
    have hnat : (541448123 : ℕ)^2127*400000000000^1615 ≤ 178298193093^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541448123 1000000000 178298193093 400000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305698541/10000000000 : ℝ), (-1955536/9765625 : ℝ), (541448123/1000000000 : ℝ)] ![(21699428709159/50000000000000 : ℝ), (120265942961/1000000000000 : ℝ), (178298193093/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305698541/10000000000 : ℝ)|^2127 ≤ (21699428709159/50000000000000 : ℝ)^1615
        have hw : |(5305698541/10000000000 : ℝ)|=(5305698541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955536/9765625 : ℝ)|^2127 ≤ (120265942961/1000000000000 : ℝ)^1615
        have hw : |(-1955536/9765625 : ℝ)|=(1955536/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541448123/1000000000 : ℝ)|^2127 ≤ (178298193093/400000000000 : ℝ)^1615
        have hw : |(541448123/1000000000 : ℝ)|=(541448123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s8_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663212323/1250000000 : ℝ)*x 0 + (5414481271/10000000000 : ℝ)*x 1 + (-2002468749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663212323/1250000000 : ℝ)^2127 ≤ (43398857881551/100000000000000 : ℝ)^1615 := by
    have hnat : (663212323 : ℕ)^2127*100000000000000^1615 ≤ 43398857881551^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663212323 1250000000 43398857881551 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414481271/10000000000 : ℝ)^2127 ≤ (11143637179447/25000000000000 : ℝ)^1615 := by
    have hnat : (5414481271 : ℕ)^2127*25000000000000^1615 ≤ 11143637179447^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414481271 10000000000 11143637179447 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2002468749/10000000000 : ℝ)^2127 ≤ (601329669323/5000000000000 : ℝ)^1615 := by
    have hnat : (2002468749 : ℕ)^2127*5000000000000^1615 ≤ 601329669323^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002468749 10000000000 601329669323 5000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663212323/1250000000 : ℝ), (5414481271/10000000000 : ℝ), (-2002468749/10000000000 : ℝ)] ![(43398857881551/100000000000000 : ℝ), (11143637179447/25000000000000 : ℝ), (601329669323/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663212323/1250000000 : ℝ)|^2127 ≤ (43398857881551/100000000000000 : ℝ)^1615
        have hw : |(663212323/1250000000 : ℝ)|=(663212323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414481271/10000000000 : ℝ)|^2127 ≤ (11143637179447/25000000000000 : ℝ)^1615
        have hw : |(5414481271/10000000000 : ℝ)|=(5414481271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2002468749/10000000000 : ℝ)|^2127 ≤ (601329669323/5000000000000 : ℝ)^1615
        have hw : |(-2002468749/10000000000 : ℝ)|=(2002468749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_s8_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2169679261/5000000000 : ℝ)*x 0 + (4518406431/10000000000 : ℝ)*x 1 + (2083576009/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169679261/5000000000 : ℝ)^2127 ≤ (260177271683/781250000000 : ℝ)^1615 := by
    have hnat : (2169679261 : ℕ)^2127*781250000000^1615 ≤ 260177271683^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169679261 5000000000 260177271683 781250000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518406431/10000000000 : ℝ)^2127 ≤ (7024833146317/20000000000000 : ℝ)^1615 := by
    have hnat : (4518406431 : ℕ)^2127*20000000000000^1615 ≤ 7024833146317^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518406431 10000000000 7024833146317 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083576009/5000000000 : ℝ)^2127 ≤ (31573143474623/100000000000000 : ℝ)^1615 := by
    have hnat : (2083576009 : ℕ)^2127*100000000000000^1615 ≤ 31573143474623^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083576009 5000000000 31573143474623 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169679261/5000000000 : ℝ), (4518406431/10000000000 : ℝ), (2083576009/5000000000 : ℝ)] ![(260177271683/781250000000 : ℝ), (7024833146317/20000000000000 : ℝ), (31573143474623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169679261/5000000000 : ℝ)|^2127 ≤ (260177271683/781250000000 : ℝ)^1615
        have hw : |(2169679261/5000000000 : ℝ)|=(2169679261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518406431/10000000000 : ℝ)|^2127 ≤ (7024833146317/20000000000000 : ℝ)^1615
        have hw : |(4518406431/10000000000 : ℝ)|=(4518406431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083576009/5000000000 : ℝ)|^2127 ≤ (31573143474623/100000000000000 : ℝ)^1615
        have hw : |(2083576009/5000000000 : ℝ)|=(2083576009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14673/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7337/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7337/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11033/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (10568174096760983/100000000000000000000 : ℝ) := by
    have hpowers : (11033/100000 : ℝ)^4253 ≤ (10568174096760983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11033 : ℕ)^4253*100000000000000000000^1024 ≤ 10568174096760983^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11033 100000 10568174096760983 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11033/100000 : ℝ)) (X := (10568174096760983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7337/50000 : ℝ) ^ (4253/1024 : ℝ) ≤ (8636723685628731/25000000000000000000 : ℝ) := by
    have hpowers : (7337/50000 : ℝ)^4253 ≤ (8636723685628731/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7337 : ℕ)^4253*25000000000000000000^1024 ≤ 8636723685628731^1024*50000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7337 50000 8636723685628731 25000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7337/50000 : ℝ)) (X := (8636723685628731/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010568174096760983/50000000000000000000 : ℝ) ≤ (5000254430803603/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50010568174096760983/50000000000000000000 : ℝ)^1024 ≤ (5000254430803603/5000000000000000 : ℝ)^4253 := by
      have hnat : (50010568174096760983 : ℕ)^1024*5000000000000000^4253 ≤ 5000254430803603^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010568174096760983 50000000000000000000 5000254430803603 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000254430803603/5000000000000000 : ℝ)) (X := (50010568174096760983/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045115068839275907/100000000000000000000 : ℝ) ≤ (10001086055033891/10000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (100045115068839275907/100000000000000000000 : ℝ)^1024 ≤ (10001086055033891/10000000000000000 : ℝ)^4253 := by
      have hnat : (100045115068839275907 : ℕ)^1024*10000000000000000^4253 ≤ 10001086055033891^4253*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045115068839275907 100000000000000000000 10001086055033891 10000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001086055033891/10000000000000000 : ℝ)) (X := (100045115068839275907/100000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508636723685628731/12500000000000000000 : ℝ) ≤ (312551976514393/312500000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (12508636723685628731/12500000000000000000 : ℝ)^1024 ≤ (312551976514393/312500000000000 : ℝ)^4253 := by
      have hnat : (12508636723685628731 : ℕ)^1024*312500000000000^4253 ≤ 312551976514393^4253*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508636723685628731 12500000000000000000 312551976514393 312500000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312551976514393/312500000000000 : ℝ)) (X := (12508636723685628731/12500000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10568174096760983/100000000000000000000 : ℝ) ≤ ((827252645794513769/827500000000000000 : ℝ)+2*(115438685337/72820000000000 : ℝ)*(11033/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (827252645794513769/827500000000000000 : ℝ)+2*(115438685337/72820000000000 : ℝ)*(11033/100000 : ℝ)=(5000254430803603/5000000000000000 : ℝ) by norm_num, show 1+2*(10568174096760983/100000000000000000000 : ℝ)=(50010568174096760983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8636723685628731/25000000000000000000 : ℝ)+(10568174096760983/100000000000000000000 : ℝ) ≤ ((827252645794513769/827500000000000000 : ℝ)+(115438685337/72820000000000 : ℝ)*((7337/50000 : ℝ)+(11033/100000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (827252645794513769/827500000000000000 : ℝ)+(115438685337/72820000000000 : ℝ)*((7337/50000 : ℝ)+(11033/100000 : ℝ))=(10001086055033891/10000000000000000 : ℝ) by norm_num, show 1+(8636723685628731/25000000000000000000 : ℝ)+(10568174096760983/100000000000000000000 : ℝ)=(100045115068839275907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8636723685628731/25000000000000000000 : ℝ) ≤ ((827252645794513769/827500000000000000 : ℝ)+2*(115438685337/72820000000000 : ℝ)*(7337/50000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (827252645794513769/827500000000000000 : ℝ)+2*(115438685337/72820000000000 : ℝ)*(7337/50000 : ℝ)=(312551976514393/312500000000000 : ℝ) by norm_num, show 1+2*(8636723685628731/25000000000000000000 : ℝ)=(12508636723685628731/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (827252645794513769/827500000000000000 : ℝ)*(X 1 0+X 2 0)+(115438685337/72820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (827252645794513769/827500000000000000 : ℝ)) (alpha := (115438685337/72820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (827252645794513769/827500000000000000 : ℝ)*(X 0 1+X 2 1)+(115438685337/72820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (827252645794513769/827500000000000000 : ℝ)) (alpha := (115438685337/72820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (827252645794513769/827500000000000000 : ℝ)*(X 0 2+X 1 2)+(115438685337/72820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (7337/50000 : ℝ)) (c := (827252645794513769/827500000000000000 : ℝ)) (alpha := (115438685337/72820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5349747487/10000000000 : ℝ)*X 2 0+(5243091999/10000000000 : ℝ)*X 2 1+(-2173858099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-417238787/2000000000 : ℝ)*X 0 0+(163865779/312500000 : ℝ)*X 0 1+(5414481357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305698541/10000000000 : ℝ)*X 1 0+(-1955536/9765625 : ℝ)*X 1 1+(541448123/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((663212323/1250000000 : ℝ)*X 2 0+(5414481271/10000000000 : ℝ)*X 2 1+(-2002468749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2169679261/5000000000 : ℝ)*X 0 0+(4518406431/10000000000 : ℝ)*X 0 1+(2083576009/5000000000 : ℝ)*X 0 2+(2169679261/5000000000 : ℝ)*X 1 0+(4518406431/10000000000 : ℝ)*X 1 1+(2083576009/5000000000 : ℝ)*X 1 2+(2169679261/5000000000 : ℝ)*X 2 0+(4518406431/10000000000 : ℝ)*X 2 1+(2083576009/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (533993930720504532697594893/227562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (341551577/100000000000000 : ℝ)*(base19) + (459010747/100000000000000 : ℝ)*(base23) + (25494859/50000000000000 : ℝ)*(lower1) + (6548719/50000000000000 : ℝ)*(upper2) + (31263207/100000000000000 : ℝ)*(upper3) + (1869317/25000000000000 : ℝ)*(upper5) + (2175636029778491/50000000000000 : ℝ)*(major0) + (2175636029778491/50000000000000 : ℝ)*(major1) + (2175636029778491/50000000000000 : ℝ)*(major2) + (2729211409/50000000000000 : ℝ)*(sp0) + (5855605571114899/100000000000000 : ℝ)*(sp1) + (2927802614781661/50000000000000 : ℝ)*(sp2) + (5855599653681333/100000000000000 : ℝ)*(sp3) + (711734617444919/25000000000000 : ℝ)*(sp4) + (711734617444919/25000000000000 : ℝ)*(f.failure) + (5855605571114899/100000000000000 : ℝ)*(f.sum) + (19392625154147/3641000000000000000000000000 : ℝ)*base65 + (2782161309054843369/455125000000000000000000000000000 : ℝ)*base67 + (8663739188604468369/455125000000000000000000000000000 : ℝ)*base69 + (3100735945555906631/455125000000000000000000000000000 : ℝ)*base72 + (10535510572033/1820500000000000000000000000 : ℝ)*base73 + (4237644869354843369/455125000000000000000000000000000 : ℝ)*base75 + (3789047507859593369/455125000000000000000000000000000 : ℝ)*base77 + (679121276204281631/455125000000000000000000000000000 : ℝ)*base80 + (5598895629399/728200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4407157/2500000000000000000000 : ℝ)*base90 + (4407157/2500000000000000000000 : ℝ)*base92 + (4407157/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7337/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1294_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1294_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1294_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1294_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1294_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
