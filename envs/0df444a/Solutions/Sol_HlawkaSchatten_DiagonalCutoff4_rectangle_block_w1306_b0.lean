-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:01.578436+00:00
-- url     : https://prove2.me/submissions/4398620b-1171-49ee-9b3b-c33871e8d765

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
theorem support_rectangle_w1306_s0_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-18306211/100000000 : ℝ)*x 0 + (6012610713/10000000000 : ℝ)*x 1 + (4802247541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18306211/100000000 : ℝ)^2133 ≤ (10707471719429/100000000000000 : ℝ)^1621 := by
    have hnat : (18306211 : ℕ)^2133*100000000000000^1621 ≤ 10707471719429^1621*100000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18306211 100000000 10707471719429 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6012610713/10000000000 : ℝ)^2133 ≤ (10240217552371/20000000000000 : ℝ)^1621 := by
    have hnat : (6012610713 : ℕ)^2133*20000000000000^1621 ≤ 10240217552371^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012610713 10000000000 10240217552371 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4802247541/10000000000 : ℝ)^2133 ≤ (38091440495259/100000000000000 : ℝ)^1621 := by
    have hnat : (4802247541 : ℕ)^2133*100000000000000^1621 ≤ 38091440495259^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802247541 10000000000 38091440495259 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18306211/100000000 : ℝ), (6012610713/10000000000 : ℝ), (4802247541/10000000000 : ℝ)] ![(10707471719429/100000000000000 : ℝ), (10240217552371/20000000000000 : ℝ), (38091440495259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18306211/100000000 : ℝ)|^2133 ≤ (10707471719429/100000000000000 : ℝ)^1621
        have hw : |(-18306211/100000000 : ℝ)|=(18306211/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6012610713/10000000000 : ℝ)|^2133 ≤ (10240217552371/20000000000000 : ℝ)^1621
        have hw : |(6012610713/10000000000 : ℝ)|=(6012610713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4802247541/10000000000 : ℝ)|^2133 ≤ (38091440495259/100000000000000 : ℝ)^1621
        have hw : |(4802247541/10000000000 : ℝ)|=(4802247541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5505847653/10000000000 : ℝ)*x 0 + (-2520406891/10000000000 : ℝ)*x 1 + (4802247529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5505847653/10000000000 : ℝ)^2133 ≤ (22799870061699/50000000000000 : ℝ)^1621 := by
    have hnat : (5505847653 : ℕ)^2133*50000000000000^1621 ≤ 22799870061699^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505847653 10000000000 22799870061699 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2520406891/10000000000 : ℝ)^2133 ≤ (8154409742661/50000000000000 : ℝ)^1621 := by
    have hnat : (2520406891 : ℕ)^2133*50000000000000^1621 ≤ 8154409742661^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2520406891 10000000000 8154409742661 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4802247529/10000000000 : ℝ)^2133 ≤ (3809144037001/10000000000000 : ℝ)^1621 := by
    have hnat : (4802247529 : ℕ)^2133*10000000000000^1621 ≤ 3809144037001^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802247529 10000000000 3809144037001 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5505847653/10000000000 : ℝ), (-2520406891/10000000000 : ℝ), (4802247529/10000000000 : ℝ)] ![(22799870061699/50000000000000 : ℝ), (8154409742661/50000000000000 : ℝ), (3809144037001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5505847653/10000000000 : ℝ)|^2133 ≤ (22799870061699/50000000000000 : ℝ)^1621
        have hw : |(5505847653/10000000000 : ℝ)|=(5505847653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2520406891/10000000000 : ℝ)|^2133 ≤ (8154409742661/50000000000000 : ℝ)^1621
        have hw : |(-2520406891/10000000000 : ℝ)|=(2520406891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4802247529/10000000000 : ℝ)|^2133 ≤ (3809144037001/10000000000000 : ℝ)^1621
        have hw : |(4802247529/10000000000 : ℝ)|=(4802247529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (21507217/39062500 : ℝ)*x 0 + (960449529/2000000000 : ℝ)*x 1 + (-1260203439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21507217/39062500 : ℝ)^2133 ≤ (22799869511351/50000000000000 : ℝ)^1621 := by
    have hnat : (21507217 : ℕ)^2133*50000000000000^1621 ≤ 22799869511351^1621*39062500^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21507217 39062500 22799869511351 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960449529/2000000000 : ℝ)^2133 ≤ (4761430197593/12500000000000 : ℝ)^1621 := by
    have hnat : (960449529 : ℕ)^2133*12500000000000^1621 ≤ 4761430197593^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960449529 2000000000 4761430197593 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260203439/5000000000 : ℝ)^2133 ≤ (8154409687317/50000000000000 : ℝ)^1621 := by
    have hnat : (1260203439 : ℕ)^2133*50000000000000^1621 ≤ 8154409687317^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260203439 5000000000 8154409687317 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21507217/39062500 : ℝ), (960449529/2000000000 : ℝ), (-1260203439/5000000000 : ℝ)] ![(22799869511351/50000000000000 : ℝ), (4761430197593/12500000000000 : ℝ), (8154409687317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21507217/39062500 : ℝ)|^2133 ≤ (22799869511351/50000000000000 : ℝ)^1621
        have hw : |(21507217/39062500 : ℝ)|=(21507217/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(960449529/2000000000 : ℝ)|^2133 ≤ (4761430197593/12500000000000 : ℝ)^1621
        have hw : |(960449529/2000000000 : ℝ)|=(960449529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1260203439/5000000000 : ℝ)|^2133 ≤ (8154409687317/50000000000000 : ℝ)^1621
        have hw : |(-1260203439/5000000000 : ℝ)|=(1260203439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (836837469/2000000000 : ℝ)*x 0 + (38856891/125000000 : ℝ)*x 1 + (5609448061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836837469/2000000000 : ℝ)^2133 ≤ (31775714544381/100000000000000 : ℝ)^1621 := by
    have hnat : (836837469 : ℕ)^2133*100000000000000^1621 ≤ 31775714544381^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836837469 2000000000 31775714544381 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38856891/125000000 : ℝ)^2133 ≤ (10746084663323/50000000000000 : ℝ)^1621 := by
    have hnat : (38856891 : ℕ)^2133*50000000000000^1621 ≤ 10746084663323^1621*125000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38856891 125000000 10746084663323 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5609448061/10000000000 : ℝ)^2133 ≤ (2336605805719/5000000000000 : ℝ)^1621 := by
    have hnat : (5609448061 : ℕ)^2133*5000000000000^1621 ≤ 2336605805719^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5609448061 10000000000 2336605805719 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836837469/2000000000 : ℝ), (38856891/125000000 : ℝ), (5609448061/10000000000 : ℝ)] ![(31775714544381/100000000000000 : ℝ), (10746084663323/50000000000000 : ℝ), (2336605805719/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836837469/2000000000 : ℝ)|^2133 ≤ (31775714544381/100000000000000 : ℝ)^1621
        have hw : |(836837469/2000000000 : ℝ)|=(836837469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38856891/125000000 : ℝ)|^2133 ≤ (10746084663323/50000000000000 : ℝ)^1621
        have hw : |(38856891/125000000 : ℝ)|=(38856891/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5609448061/10000000000 : ℝ)|^2133 ≤ (2336605805719/5000000000000 : ℝ)^1621
        have hw : |(5609448061/10000000000 : ℝ)|=(5609448061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-229408713/1250000000 : ℝ)*x 0 + (4833461523/10000000000 : ℝ)*x 1 + (2990142217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229408713/1250000000 : ℝ)^2133 ≤ (2148652858093/20000000000000 : ℝ)^1621 := by
    have hnat : (229408713 : ℕ)^2133*20000000000000^1621 ≤ 2148652858093^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229408713 1250000000 2148652858093 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4833461523/10000000000 : ℝ)^2133 ≤ (7683513203707/20000000000000 : ℝ)^1621 := by
    have hnat : (4833461523 : ℕ)^2133*20000000000000^1621 ≤ 7683513203707^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4833461523 10000000000 7683513203707 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2990142217/5000000000 : ℝ)^2133 ≤ (50839169667063/100000000000000 : ℝ)^1621 := by
    have hnat : (2990142217 : ℕ)^2133*100000000000000^1621 ≤ 50839169667063^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2990142217 5000000000 50839169667063 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-229408713/1250000000 : ℝ), (4833461523/10000000000 : ℝ), (2990142217/5000000000 : ℝ)] ![(2148652858093/20000000000000 : ℝ), (7683513203707/20000000000000 : ℝ), (50839169667063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-229408713/1250000000 : ℝ)|^2133 ≤ (2148652858093/20000000000000 : ℝ)^1621
        have hw : |(-229408713/1250000000 : ℝ)|=(229408713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4833461523/10000000000 : ℝ)|^2133 ≤ (7683513203707/20000000000000 : ℝ)^1621
        have hw : |(4833461523/10000000000 : ℝ)|=(4833461523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2990142217/5000000000 : ℝ)|^2133 ≤ (50839169667063/100000000000000 : ℝ)^1621
        have hw : |(2990142217/5000000000 : ℝ)|=(2990142217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1294057907/2500000000 : ℝ)*x 0 + (-335592561/2500000000 : ℝ)*x 1 + (1495071081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294057907/2500000000 : ℝ)^2133 ≤ (2102101454737/5000000000000 : ℝ)^1621 := by
    have hnat : (1294057907 : ℕ)^2133*5000000000000^1621 ≤ 2102101454737^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294057907 2500000000 2102101454737 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (335592561/2500000000 : ℝ)^2133 ≤ (7118802447537/100000000000000 : ℝ)^1621 := by
    have hnat : (335592561 : ℕ)^2133*100000000000000^1621 ≤ 7118802447537^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335592561 2500000000 7118802447537 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1495071081/2500000000 : ℝ)^2133 ≤ (2033566737463/4000000000000 : ℝ)^1621 := by
    have hnat : (1495071081 : ℕ)^2133*4000000000000^1621 ≤ 2033566737463^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1495071081 2500000000 2033566737463 4000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294057907/2500000000 : ℝ), (-335592561/2500000000 : ℝ), (1495071081/2500000000 : ℝ)] ![(2102101454737/5000000000000 : ℝ), (7118802447537/100000000000000 : ℝ), (2033566737463/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294057907/2500000000 : ℝ)|^2133 ≤ (2102101454737/5000000000000 : ℝ)^1621
        have hw : |(1294057907/2500000000 : ℝ)|=(1294057907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-335592561/2500000000 : ℝ)|^2133 ≤ (7118802447537/100000000000000 : ℝ)^1621
        have hw : |(-335592561/2500000000 : ℝ)|=(335592561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1495071081/2500000000 : ℝ)|^2133 ≤ (2033566737463/4000000000000 : ℝ)^1621
        have hw : |(1495071081/2500000000 : ℝ)|=(1495071081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (647028957/1250000000 : ℝ)*x 0 + (186883887/312500000 : ℝ)*x 1 + (-268474021/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647028957/1250000000 : ℝ)^2133 ≤ (42042029393991/100000000000000 : ℝ)^1621 := by
    have hnat : (647028957 : ℕ)^2133*100000000000000^1621 ≤ 42042029393991^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647028957 1250000000 42042029393991 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186883887/312500000 : ℝ)^2133 ≤ (203356676431/400000000000 : ℝ)^1621 := by
    have hnat : (186883887 : ℕ)^2133*400000000000^1621 ≤ 203356676431^1621*312500000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186883887 312500000 203356676431 400000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268474021/2000000000 : ℝ)^2133 ≤ (711880147757/10000000000000 : ℝ)^1621 := by
    have hnat : (268474021 : ℕ)^2133*10000000000000^1621 ≤ 711880147757^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268474021 2000000000 711880147757 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647028957/1250000000 : ℝ), (186883887/312500000 : ℝ), (-268474021/2000000000 : ℝ)] ![(42042029393991/100000000000000 : ℝ), (203356676431/400000000000 : ℝ), (711880147757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647028957/1250000000 : ℝ)|^2133 ≤ (42042029393991/100000000000000 : ℝ)^1621
        have hw : |(647028957/1250000000 : ℝ)|=(647028957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186883887/312500000 : ℝ)|^2133 ≤ (203356676431/400000000000 : ℝ)^1621
        have hw : |(186883887/312500000 : ℝ)|=(186883887/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268474021/2000000000 : ℝ)|^2133 ≤ (711880147757/10000000000000 : ℝ)^1621
        have hw : |(-268474021/2000000000 : ℝ)|=(268474021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s0_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2096895957/5000000000 : ℝ)*x 0 + (2772476491/5000000000 : ℝ)*x 1 + (1587672399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096895957/5000000000 : ℝ)^2133 ≤ (6374345385607/20000000000000 : ℝ)^1621 := by
    have hnat : (2096895957 : ℕ)^2133*20000000000000^1621 ≤ 6374345385607^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096895957 5000000000 6374345385607 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2772476491/5000000000 : ℝ)^2133 ≤ (46026386480987/100000000000000 : ℝ)^1621 := by
    have hnat : (2772476491 : ℕ)^2133*100000000000000^1621 ≤ 46026386480987^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772476491 5000000000 46026386480987 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587672399/5000000000 : ℝ)^2133 ≤ (1381367910633/6250000000000 : ℝ)^1621 := by
    have hnat : (1587672399 : ℕ)^2133*6250000000000^1621 ≤ 1381367910633^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587672399 5000000000 1381367910633 6250000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096895957/5000000000 : ℝ), (2772476491/5000000000 : ℝ), (1587672399/5000000000 : ℝ)] ![(6374345385607/20000000000000 : ℝ), (46026386480987/100000000000000 : ℝ), (1381367910633/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096895957/5000000000 : ℝ)|^2133 ≤ (6374345385607/20000000000000 : ℝ)^1621
        have hw : |(2096895957/5000000000 : ℝ)|=(2096895957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2772476491/5000000000 : ℝ)|^2133 ≤ (46026386480987/100000000000000 : ℝ)^1621
        have hw : |(2772476491/5000000000 : ℝ)|=(2772476491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587672399/5000000000 : ℝ)|^2133 ≤ (1381367910633/6250000000000 : ℝ)^1621
        have hw : |(1587672399/5000000000 : ℝ)|=(1587672399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6783/25000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4265/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4265 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4265*1^1024 ≤ 0^1024*1^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4265/1024 : ℝ) ≤ (275089701685968051/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4265 ≤ (275089701685968051/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4265*12500000000000000000^1024 ≤ 275089701685968051^1024*5^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 275089701685968051 12500000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (275089701685968051/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4265 := by
      have hnat : (1 : ℕ)^1024*1^4265 ≤ 1^4265*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12775089701685968051/12500000000000000000 : ℝ) ≤ (5026200833563727/5000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (12775089701685968051/12500000000000000000 : ℝ)^1024 ≤ (5026200833563727/5000000000000000 : ℝ)^4265 := by
      have hnat : (12775089701685968051 : ℕ)^1024*5000000000000000^4265 ≤ 5026200833563727^4265*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12775089701685968051 12500000000000000000 5026200833563727 5000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026200833563727/5000000000000000 : ℝ)) (X := (12775089701685968051/12500000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6525089701685968051/6250000000000000000 : ℝ) ≤ (2526200833563727/2500000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (6525089701685968051/6250000000000000000 : ℝ)^1024 ≤ (2526200833563727/2500000000000000 : ℝ)^4265 := by
      have hnat : (6525089701685968051 : ℕ)^1024*2500000000000000^4265 ≤ 2526200833563727^4265*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6525089701685968051 6250000000000000000 2526200833563727 2500000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526200833563727/2500000000000000 : ℝ)) (X := (6525089701685968051/6250000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26200833563727/2000000000000000 : ℝ)*(0 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26200833563727/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(275089701685968051/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26200833563727/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26200833563727/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5026200833563727/5000000000000000 : ℝ) by norm_num, show 1+(275089701685968051/12500000000000000000 : ℝ)+(0 : ℝ)=(12775089701685968051/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(275089701685968051/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26200833563727/2000000000000000 : ℝ)*(2/5 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26200833563727/2000000000000000 : ℝ)*(2/5 : ℝ)=(2526200833563727/2500000000000000 : ℝ) by norm_num, show 1+2*(275089701685968051/12500000000000000000 : ℝ)=(6525089701685968051/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26200833563727/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26200833563727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26200833563727/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26200833563727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26200833563727/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26200833563727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-18306211/100000000 : ℝ)*X 0 0+(6012610713/10000000000 : ℝ)*X 0 1+(4802247541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5505847653/10000000000 : ℝ)*X 1 0+(-2520406891/10000000000 : ℝ)*X 1 1+(4802247529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21507217/39062500 : ℝ)*X 2 0+(960449529/2000000000 : ℝ)*X 2 1+(-1260203439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((836837469/2000000000 : ℝ)*X 0 0+(38856891/125000000 : ℝ)*X 0 1+(5609448061/10000000000 : ℝ)*X 0 2+(836837469/2000000000 : ℝ)*X 1 0+(38856891/125000000 : ℝ)*X 1 1+(5609448061/10000000000 : ℝ)*X 1 2+(836837469/2000000000 : ℝ)*X 2 0+(38856891/125000000 : ℝ)*X 2 1+(5609448061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-229408713/1250000000 : ℝ)*X 0 0+(4833461523/10000000000 : ℝ)*X 0 1+(2990142217/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294057907/2500000000 : ℝ)*X 1 0+(-335592561/2500000000 : ℝ)*X 1 1+(1495071081/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647028957/1250000000 : ℝ)*X 2 0+(186883887/312500000 : ℝ)*X 2 1+(-268474021/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2096895957/5000000000 : ℝ)*X 0 0+(2772476491/5000000000 : ℝ)*X 0 1+(1587672399/5000000000 : ℝ)*X 0 2+(2096895957/5000000000 : ℝ)*X 1 0+(2772476491/5000000000 : ℝ)*X 1 1+(1587672399/5000000000 : ℝ)*X 1 2+(2096895957/5000000000 : ℝ)*X 2 0+(2772476491/5000000000 : ℝ)*X 2 1+(1587672399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51026923194063029133111/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33528209/100000000000000 : ℝ)*(base1) + (131381493/25000000000000 : ℝ)*(base19) + (510370031/100000000000000 : ℝ)*(base23) + (6018599/10000000000000 : ℝ)*(upper3) + (29226659/50000000000000 : ℝ)*(upper5) + (153257460013469/25000000000000 : ℝ)*(major0) + (153257460013469/25000000000000 : ℝ)*(major1) + (153257460013469/25000000000000 : ℝ)*(major2) + (2581874712253/312500000000 : ℝ)*(sp0) + (413100505803293/50000000000000 : ℝ)*(sp1) + (25818782086329/3125000000000 : ℝ)*(sp2) + (12495540192269/3125000000000 : ℝ)*(sp3) + (51960619/3125000000000 : ℝ)*(sp4) + (94407309/12500000000000 : ℝ)*(sp7) + (399858074939289/100000000000000 : ℝ)*(f.failure) + (413100768566279/50000000000000 : ℝ)*(f.sum) + (16667981438963/25000000000000000000000000000 : ℝ)*base65 + (290447000561037/50000000000000000000000000000 : ℝ)*base68 + (174019201038963/50000000000000000000000000000 : ℝ)*base69 + (133511498538963/50000000000000000000000000000 : ℝ)*base71 + (103707250611037/25000000000000000000000000000 : ℝ)*base74 + (184933302938963/50000000000000000000000000000 : ℝ)*base75 + (65822941361037/50000000000000000000000000000 : ℝ)*base78 + (274476725361037/50000000000000000000000000000 : ℝ)*base80 + (155619335838963/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (41150327/10000000000000000000000 : ℝ)*base90 + (41150327/10000000000000000000000 : ℝ)*base92 + (41150327/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44916734308047961786023/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (421917963/100000000000000 : ℝ)*(base19) + (90324109/20000000000000 : ℝ)*(base23) + (10165957/50000000000000 : ℝ)*(base39) + (2029447/4000000000000 : ℝ)*(upper3) + (27857713/50000000000000 : ℝ)*(upper5) + (323496213096917/50000000000000 : ℝ)*(major0) + (323496213096917/50000000000000 : ℝ)*(major1) + (4043702536637/625000000000 : ℝ)*(major2) + (231892449/25000000000000 : ℝ)*(sp1) + (504367237/50000000000000 : ℝ)*(sp2) + (871974081764761/100000000000000 : ℝ)*(sp4) + (871972732277/100000000000 : ℝ)*(sp5) + (108996580217707/12500000000000 : ℝ)*(sp6) + (105502672600501/25000000000000 : ℝ)*(sp7) + (105502672600501/25000000000000 : ℝ)*(f.failure) + (435987051048337/50000000000000 : ℝ)*(f.sum) + (315682196817579/100000000000000000000000000000 : ℝ)*base65 + (2143216897651/1250000000000000000000000000 : ℝ)*base68 + (146031800129659/100000000000000000000000000000 : ℝ)*base69 + (9291191211099/1250000000000000000000000000 : ℝ)*base71 + (174780681182421/100000000000000000000000000000 : ℝ)*base74 + (1217656619129659/100000000000000000000000000000 : ℝ)*base75 + (1195782729659/100000000000000000000000000000 : ℝ)*base77 + (214596609470341/100000000000000000000000000000 : ℝ)*base80 + (212988889729659/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (22559643/2500000000000000000000 : ℝ)*base90 + (22559643/2500000000000000000000 : ℝ)*base92 + (22559643/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1306_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6783/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1306_s1_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-80825721/400000000 : ℝ)*x 0 + (2829328921/5000000000 : ℝ)*x 1 + (157329331/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80825721/400000000 : ℝ)^2133 ≤ (12193416865207/100000000000000 : ℝ)^1621 := by
    have hnat : (80825721 : ℕ)^2133*100000000000000^1621 ≤ 12193416865207^1621*400000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80825721 400000000 12193416865207 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829328921/5000000000 : ℝ)^2133 ≤ (47272316219597/100000000000000 : ℝ)^1621 := by
    have hnat : (2829328921 : ℕ)^2133*100000000000000^1621 ≤ 47272316219597^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829328921 5000000000 47272316219597 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157329331/312500000 : ℝ)^2133 ≤ (4053426689703/10000000000000 : ℝ)^1621 := by
    have hnat : (157329331 : ℕ)^2133*10000000000000^1621 ≤ 4053426689703^1621*312500000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157329331 312500000 4053426689703 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80825721/400000000 : ℝ), (2829328921/5000000000 : ℝ), (157329331/312500000 : ℝ)] ![(12193416865207/100000000000000 : ℝ), (47272316219597/100000000000000 : ℝ), (4053426689703/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80825721/400000000 : ℝ)|^2133 ≤ (12193416865207/100000000000000 : ℝ)^1621
        have hw : |(-80825721/400000000 : ℝ)|=(80825721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829328921/5000000000 : ℝ)|^2133 ≤ (47272316219597/100000000000000 : ℝ)^1621
        have hw : |(2829328921/5000000000 : ℝ)|=(2829328921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157329331/312500000 : ℝ)|^2133 ≤ (4053426689703/10000000000000 : ℝ)^1621
        have hw : |(157329331/312500000 : ℝ)|=(157329331/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5409497767/10000000000 : ℝ)*x 0 + (-235473771/1000000000 : ℝ)*x 1 + (1006907763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409497767/10000000000 : ℝ)^2133 ≤ (4455263452377/10000000000000 : ℝ)^1621 := by
    have hnat : (5409497767 : ℕ)^2133*10000000000000^1621 ≤ 4455263452377^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409497767 10000000000 4455263452377 10000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235473771/1000000000 : ℝ)^2133 ≤ (596523848187/4000000000000 : ℝ)^1621 := by
    have hnat : (235473771 : ℕ)^2133*4000000000000^1621 ≤ 596523848187^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235473771 1000000000 596523848187 4000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006907763/2000000000 : ℝ)^2133 ≤ (40534269259549/100000000000000 : ℝ)^1621 := by
    have hnat : (1006907763 : ℕ)^2133*100000000000000^1621 ≤ 40534269259549^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006907763 2000000000 40534269259549 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409497767/10000000000 : ℝ), (-235473771/1000000000 : ℝ), (1006907763/2000000000 : ℝ)] ![(4455263452377/10000000000000 : ℝ), (596523848187/4000000000000 : ℝ), (40534269259549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409497767/10000000000 : ℝ)|^2133 ≤ (4455263452377/10000000000000 : ℝ)^1621
        have hw : |(5409497767/10000000000 : ℝ)|=(5409497767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235473771/1000000000 : ℝ)|^2133 ≤ (596523848187/4000000000000 : ℝ)^1621
        have hw : |(-235473771/1000000000 : ℝ)|=(235473771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006907763/2000000000 : ℝ)|^2133 ≤ (40534269259549/100000000000000 : ℝ)^1621
        have hw : |(1006907763/2000000000 : ℝ)|=(1006907763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (676187257/1250000000 : ℝ)*x 0 + (314658647/625000000 : ℝ)*x 1 + (-1177368961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676187257/1250000000 : ℝ)^2133 ≤ (44552637655773/100000000000000 : ℝ)^1621 := by
    have hnat : (676187257 : ℕ)^2133*100000000000000^1621 ≤ 44552637655773^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676187257 1250000000 44552637655773 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314658647/625000000 : ℝ)^2133 ≤ (5066783044301/12500000000000 : ℝ)^1621 := by
    have hnat : (314658647 : ℕ)^2133*12500000000000^1621 ≤ 5066783044301^1621*625000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314658647 625000000 5066783044301 12500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1177368961/5000000000 : ℝ)^2133 ≤ (74565489857/500000000000 : ℝ)^1621 := by
    have hnat : (1177368961 : ℕ)^2133*500000000000^1621 ≤ 74565489857^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177368961 5000000000 74565489857 500000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676187257/1250000000 : ℝ), (314658647/625000000 : ℝ), (-1177368961/5000000000 : ℝ)] ![(44552637655773/100000000000000 : ℝ), (5066783044301/12500000000000 : ℝ), (74565489857/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676187257/1250000000 : ℝ)|^2133 ≤ (44552637655773/100000000000000 : ℝ)^1621
        have hw : |(676187257/1250000000 : ℝ)|=(676187257/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314658647/625000000 : ℝ)|^2133 ≤ (5066783044301/12500000000000 : ℝ)^1621
        have hw : |(314658647/625000000 : ℝ)|=(314658647/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1177368961/5000000000 : ℝ)|^2133 ≤ (74565489857/500000000000 : ℝ)^1621
        have hw : |(-1177368961/5000000000 : ℝ)|=(1177368961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298686177/10000000000 : ℝ)*x 0 + (184971313/500000000 : ℝ)*x 1 + (4989004591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298686177/10000000000 : ℝ)^2133 ≤ (32924805441287/100000000000000 : ℝ)^1621 := by
    have hnat : (4298686177 : ℕ)^2133*100000000000000^1621 ≤ 32924805441287^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298686177 10000000000 32924805441287 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184971313/500000000 : ℝ)^2133 ≤ (27022636077203/100000000000000 : ℝ)^1621 := by
    have hnat : (184971313 : ℕ)^2133*100000000000000^1621 ≤ 27022636077203^1621*500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184971313 500000000 27022636077203 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4989004591/10000000000 : ℝ)^2133 ≤ (40052558463369/100000000000000 : ℝ)^1621 := by
    have hnat : (4989004591 : ℕ)^2133*100000000000000^1621 ≤ 40052558463369^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989004591 10000000000 40052558463369 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298686177/10000000000 : ℝ), (184971313/500000000 : ℝ), (4989004591/10000000000 : ℝ)] ![(32924805441287/100000000000000 : ℝ), (27022636077203/100000000000000 : ℝ), (40052558463369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298686177/10000000000 : ℝ)|^2133 ≤ (32924805441287/100000000000000 : ℝ)^1621
        have hw : |(4298686177/10000000000 : ℝ)|=(4298686177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184971313/500000000 : ℝ)|^2133 ≤ (27022636077203/100000000000000 : ℝ)^1621
        have hw : |(184971313/500000000 : ℝ)|=(184971313/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4989004591/10000000000 : ℝ)|^2133 ≤ (40052558463369/100000000000000 : ℝ)^1621
        have hw : |(4989004591/10000000000 : ℝ)|=(4989004591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2021250253/10000000000 : ℝ)*x 0 + (1008517803/2000000000 : ℝ)*x 1 + (2825228339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2021250253/10000000000 : ℝ)^2133 ≤ (11912342521/97656250000 : ℝ)^1621 := by
    have hnat : (2021250253 : ℕ)^2133*97656250000^1621 ≤ 11912342521^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021250253 10000000000 11912342521 97656250000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008517803/2000000000 : ℝ)^2133 ≤ (40619576674461/100000000000000 : ℝ)^1621 := by
    have hnat : (1008517803 : ℕ)^2133*100000000000000^1621 ≤ 40619576674461^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008517803 2000000000 40619576674461 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2825228339/5000000000 : ℝ)^2133 ≤ (23591092283233/50000000000000 : ℝ)^1621 := by
    have hnat : (2825228339 : ℕ)^2133*50000000000000^1621 ≤ 23591092283233^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825228339 5000000000 23591092283233 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2021250253/10000000000 : ℝ), (1008517803/2000000000 : ℝ), (2825228339/5000000000 : ℝ)] ![(11912342521/97656250000 : ℝ), (40619576674461/100000000000000 : ℝ), (23591092283233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2021250253/10000000000 : ℝ)|^2133 ≤ (11912342521/97656250000 : ℝ)^1621
        have hw : |(-2021250253/10000000000 : ℝ)|=(2021250253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1008517803/2000000000 : ℝ)|^2133 ≤ (40619576674461/100000000000000 : ℝ)^1621
        have hw : |(1008517803/2000000000 : ℝ)|=(1008517803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2825228339/5000000000 : ℝ)|^2133 ≤ (23591092283233/50000000000000 : ℝ)^1621
        have hw : |(2825228339/5000000000 : ℝ)|=(2825228339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1312011721/2500000000 : ℝ)*x 0 + (-1738818947/10000000000 : ℝ)*x 1 + (5650457471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312011721/2500000000 : ℝ)^2133 ≤ (21405617021971/50000000000000 : ℝ)^1621 := by
    have hnat : (1312011721 : ℕ)^2133*50000000000000^1621 ≤ 21405617021971^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312011721 2500000000 21405617021971 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1738818947/10000000000 : ℝ)^2133 ≤ (10006572666399/100000000000000 : ℝ)^1621 := by
    have hnat : (1738818947 : ℕ)^2133*100000000000000^1621 ≤ 10006572666399^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738818947 10000000000 10006572666399 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5650457471/10000000000 : ℝ)^2133 ≤ (47182193279623/100000000000000 : ℝ)^1621 := by
    have hnat : (5650457471 : ℕ)^2133*100000000000000^1621 ≤ 47182193279623^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650457471 10000000000 47182193279623 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312011721/2500000000 : ℝ), (-1738818947/10000000000 : ℝ), (5650457471/10000000000 : ℝ)] ![(21405617021971/50000000000000 : ℝ), (10006572666399/100000000000000 : ℝ), (47182193279623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312011721/2500000000 : ℝ)|^2133 ≤ (21405617021971/50000000000000 : ℝ)^1621
        have hw : |(1312011721/2500000000 : ℝ)|=(1312011721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1738818947/10000000000 : ℝ)|^2133 ≤ (10006572666399/100000000000000 : ℝ)^1621
        have hw : |(-1738818947/10000000000 : ℝ)|=(1738818947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5650457471/10000000000 : ℝ)|^2133 ≤ (47182193279623/100000000000000 : ℝ)^1621
        have hw : |(5650457471/10000000000 : ℝ)|=(5650457471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2624023403/5000000000 : ℝ)*x 0 + (5650457057/10000000000 : ℝ)*x 1 + (-1738819657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2624023403/5000000000 : ℝ)^2133 ≤ (21405616603339/50000000000000 : ℝ)^1621 := by
    have hnat : (2624023403 : ℕ)^2133*50000000000000^1621 ≤ 21405616603339^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624023403 5000000000 21405616603339 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5650457057/10000000000 : ℝ)^2133 ≤ (47182188730761/100000000000000 : ℝ)^1621 := by
    have hnat : (5650457057 : ℕ)^2133*100000000000000^1621 ≤ 47182188730761^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5650457057 10000000000 47182188730761 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1738819657/10000000000 : ℝ)^2133 ≤ (2501644510717/25000000000000 : ℝ)^1621 := by
    have hnat : (1738819657 : ℕ)^2133*25000000000000^1621 ≤ 2501644510717^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738819657 10000000000 2501644510717 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2624023403/5000000000 : ℝ), (5650457057/10000000000 : ℝ), (-1738819657/10000000000 : ℝ)] ![(21405616603339/50000000000000 : ℝ), (47182188730761/100000000000000 : ℝ), (2501644510717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2624023403/5000000000 : ℝ)|^2133 ≤ (21405616603339/50000000000000 : ℝ)^1621
        have hw : |(2624023403/5000000000 : ℝ)|=(2624023403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5650457057/10000000000 : ℝ)|^2133 ≤ (47182188730761/100000000000000 : ℝ)^1621
        have hw : |(5650457057/10000000000 : ℝ)|=(5650457057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1738819657/10000000000 : ℝ)|^2133 ≤ (2501644510717/25000000000000 : ℝ)^1621
        have hw : |(-1738819657/10000000000 : ℝ)|=(1738819657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s1_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2149969927/5000000000 : ℝ)*x 0 + (4972371069/10000000000 : ℝ)*x 1 + (3716371071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149969927/5000000000 : ℝ)^2133 ≤ (16468720594941/50000000000000 : ℝ)^1621 := by
    have hnat : (2149969927 : ℕ)^2133*50000000000000^1621 ≤ 16468720594941^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149969927 5000000000 16468720594941 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4972371069/10000000000 : ℝ)^2133 ≤ (7975387244741/20000000000000 : ℝ)^1621 := by
    have hnat : (4972371069 : ℕ)^2133*20000000000000^1621 ≤ 7975387244741^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4972371069 10000000000 7975387244741 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3716371071/10000000000 : ℝ)^2133 ≤ (13592811286227/50000000000000 : ℝ)^1621 := by
    have hnat : (3716371071 : ℕ)^2133*50000000000000^1621 ≤ 13592811286227^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3716371071 10000000000 13592811286227 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149969927/5000000000 : ℝ), (4972371069/10000000000 : ℝ), (3716371071/10000000000 : ℝ)] ![(16468720594941/50000000000000 : ℝ), (7975387244741/20000000000000 : ℝ), (13592811286227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149969927/5000000000 : ℝ)|^2133 ≤ (16468720594941/50000000000000 : ℝ)^1621
        have hw : |(2149969927/5000000000 : ℝ)|=(2149969927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4972371069/10000000000 : ℝ)|^2133 ≤ (7975387244741/20000000000000 : ℝ)^1621
        have hw : |(4972371069/10000000000 : ℝ)|=(4972371069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3716371071/10000000000 : ℝ)|^2133 ≤ (13592811286227/50000000000000 : ℝ)^1621
        have hw : |(3716371071/10000000000 : ℝ)|=(3716371071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6783/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6547/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9869/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6783/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6783/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6783/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6783/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6783/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6783/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1141/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (810063047933/100000000000000000000 : ℝ) := by
    have hpowers : (1141/100000 : ℝ)^4265 ≤ (810063047933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1141 : ℕ)^4265*100000000000000000000^1024 ≤ 810063047933^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1141 100000 810063047933 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1141/100000 : ℝ)) (X := (810063047933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6783/25000 : ℝ) ^ (4265/1024 : ℝ) ≤ (436947845568518681/100000000000000000000 : ℝ) := by
    have hpowers : (6783/25000 : ℝ)^4265 ≤ (436947845568518681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6783 : ℕ)^4265*100000000000000000000^1024 ≤ 436947845568518681^1024*25000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6783 25000 436947845568518681 100000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6783/25000 : ℝ)) (X := (436947845568518681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000810063047933/50000000000000000000 : ℝ) ≤ (10000000038898221/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50000000810063047933/50000000000000000000 : ℝ)^1024 ≤ (10000000038898221/10000000000000000 : ℝ)^4265 := by
      have hnat : (50000000810063047933 : ℕ)^1024*10000000000000000^4265 ≤ 10000000038898221^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000810063047933 50000000000000000000 10000000038898221 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000038898221/10000000000000000 : ℝ)) (X := (50000000810063047933/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50218474327815783307/50000000000000000000 : ℝ) ≤ (5005236746652491/5000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50218474327815783307/50000000000000000000 : ℝ)^1024 ≤ (5005236746652491/5000000000000000 : ℝ)^4265 := by
      have hnat : (50218474327815783307 : ℕ)^1024*5000000000000000^4265 ≤ 5005236746652491^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50218474327815783307 50000000000000000000 5005236746652491 5000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005236746652491/5000000000000000 : ℝ)) (X := (50218474327815783307/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50436947845568518681/50000000000000000000 : ℝ) ≤ (10020946947711743/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (50436947845568518681/50000000000000000000 : ℝ)^1024 ≤ (10020946947711743/10000000000000000 : ℝ)^4265 := by
      have hnat : (50436947845568518681 : ℕ)^1024*10000000000000000^4265 ≤ 10020946947711743^4265*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50436947845568518681 50000000000000000000 10020946947711743 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10020946947711743/10000000000000000 : ℝ)) (X := (50436947845568518681/50000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(810063047933/100000000000000000000 : ℝ) ≤ ((789927357410478521/790000000000000000 : ℝ)+2*(222839455463/55300000000000 : ℝ)*(1141/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (789927357410478521/790000000000000000 : ℝ)+2*(222839455463/55300000000000 : ℝ)*(1141/100000 : ℝ)=(10000000038898221/10000000000000000 : ℝ) by norm_num, show 1+2*(810063047933/100000000000000000000 : ℝ)=(50000000810063047933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(436947845568518681/100000000000000000000 : ℝ)+(810063047933/100000000000000000000 : ℝ) ≤ ((789927357410478521/790000000000000000 : ℝ)+(222839455463/55300000000000 : ℝ)*((6783/25000 : ℝ)+(1141/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (789927357410478521/790000000000000000 : ℝ)+(222839455463/55300000000000 : ℝ)*((6783/25000 : ℝ)+(1141/100000 : ℝ))=(5005236746652491/5000000000000000 : ℝ) by norm_num, show 1+(436947845568518681/100000000000000000000 : ℝ)+(810063047933/100000000000000000000 : ℝ)=(50218474327815783307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(436947845568518681/100000000000000000000 : ℝ) ≤ ((789927357410478521/790000000000000000 : ℝ)+2*(222839455463/55300000000000 : ℝ)*(6783/25000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (789927357410478521/790000000000000000 : ℝ)+2*(222839455463/55300000000000 : ℝ)*(6783/25000 : ℝ)=(10020946947711743/10000000000000000 : ℝ) by norm_num, show 1+2*(436947845568518681/100000000000000000000 : ℝ)=(50436947845568518681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (789927357410478521/790000000000000000 : ℝ)*(X 1 0+X 2 0)+(222839455463/55300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (1141/100000 : ℝ)) (hi := (6783/25000 : ℝ)) (c := (789927357410478521/790000000000000000 : ℝ)) (alpha := (222839455463/55300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (789927357410478521/790000000000000000 : ℝ)*(X 0 1+X 2 1)+(222839455463/55300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (1141/100000 : ℝ)) (hi := (6783/25000 : ℝ)) (c := (789927357410478521/790000000000000000 : ℝ)) (alpha := (222839455463/55300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (789927357410478521/790000000000000000 : ℝ)*(X 0 2+X 1 2)+(222839455463/55300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (1141/100000 : ℝ)) (hi := (6783/25000 : ℝ)) (c := (789927357410478521/790000000000000000 : ℝ)) (alpha := (222839455463/55300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-80825721/400000000 : ℝ)*X 0 0+(2829328921/5000000000 : ℝ)*X 0 1+(157329331/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5409497767/10000000000 : ℝ)*X 1 0+(-235473771/1000000000 : ℝ)*X 1 1+(1006907763/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676187257/1250000000 : ℝ)*X 2 0+(314658647/625000000 : ℝ)*X 2 1+(-1177368961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298686177/10000000000 : ℝ)*X 0 0+(184971313/500000000 : ℝ)*X 0 1+(4989004591/10000000000 : ℝ)*X 0 2+(4298686177/10000000000 : ℝ)*X 1 0+(184971313/500000000 : ℝ)*X 1 1+(4989004591/10000000000 : ℝ)*X 1 2+(4298686177/10000000000 : ℝ)*X 2 0+(184971313/500000000 : ℝ)*X 2 1+(4989004591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2021250253/10000000000 : ℝ)*X 0 0+(1008517803/2000000000 : ℝ)*X 0 1+(2825228339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1312011721/2500000000 : ℝ)*X 1 0+(-1738818947/10000000000 : ℝ)*X 1 1+(5650457471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2624023403/5000000000 : ℝ)*X 2 0+(5650457057/10000000000 : ℝ)*X 2 1+(-1738819657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2149969927/5000000000 : ℝ)*X 0 0+(4972371069/10000000000 : ℝ)*X 0 1+(3716371071/10000000000 : ℝ)*X 0 2+(2149969927/5000000000 : ℝ)*X 1 0+(4972371069/10000000000 : ℝ)*X 1 1+(3716371071/10000000000 : ℝ)*X 1 2+(2149969927/5000000000 : ℝ)*X 2 0+(4972371069/10000000000 : ℝ)*X 2 1+(3716371071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (193473437965866610139211843/34562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58771631/100000000000000 : ℝ)*(base1) + (228587747/25000000000000 : ℝ)*(base19) + (999951387/100000000000000 : ℝ)*(base23) + (79097191/50000000000000 : ℝ)*(upper3) + (1197049/1250000000000 : ℝ)*(upper5) + (297215053884277/25000000000000 : ℝ)*(major0) + (297215053884277/25000000000000 : ℝ)*(major1) + (297215053884277/25000000000000 : ℝ)*(major2) + (1602263169546609/100000000000000 : ℝ)*(sp0) + (200283387387787/12500000000000 : ℝ)*(sp1) + (1602267013501897/100000000000000 : ℝ)*(sp2) + (31017979971383/4000000000000 : ℝ)*(sp3) + (2451339153/50000000000000 : ℝ)*(sp4) + (668242973/25000000000000 : ℝ)*(sp7) + (387726115514049/50000000000000 : ℝ)*(f.failure) + (400567003363321/25000000000000 : ℝ)*(f.sum) + (3643421797/86406250000000000000000000 : ℝ)*base65 + (585858935809900219/138250000000000000000000000000000 : ℝ)*base67 + (824370084169650219/138250000000000000000000000000000 : ℝ)*base69 + (638714930328150219/138250000000000000000000000000000 : ℝ)*base71 + (1183381154829/691250000000000000000000000 : ℝ)*base74 + (203495245186650219/138250000000000000000000000000000 : ℝ)*base75 + (686101610928150219/138250000000000000000000000000000 : ℝ)*base77 + (486198943922099781/138250000000000000000000000000000 : ℝ)*base80 + (1984230250909/2765000000000000000000000000 : ℝ)*base81 + (38221007/5000000000000000000000 : ℝ)*base90 + (38221007/5000000000000000000000 : ℝ)*base92 + (38221007/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (450593982432091374978419739/138250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97678551/20000000000000 : ℝ)*(base19) + (546737957/100000000000000 : ℝ)*(base23) + (14569921/25000000000000 : ℝ)*(upper2) + (134103637/100000000000000 : ℝ)*(upper3) + (62656833/100000000000000 : ℝ)*(upper5) + (610318033397479/50000000000000 : ℝ)*(major0) + (610318033397479/50000000000000 : ℝ)*(major1) + (610318033397479/50000000000000 : ℝ)*(major2) + (1694873033/50000000000000 : ℝ)*(sp1) + (247131109/10000000000000 : ℝ)*(sp2) + (411273377419483/25000000000000 : ℝ)*(sp4) + (164508963153911/10000000000000 : ℝ)*(sp5) + (411272622907221/25000000000000 : ℝ)*(sp6) + (796178515269669/100000000000000 : ℝ)*(sp7) + (796178515269669/100000000000000 : ℝ)*(f.failure) + (411273377419483/25000000000000 : ℝ)*(f.sum) + (12252572653/86406250000000000000000000 : ℝ)*base66 + (2239711849213460087/276500000000000000000000000000000 : ℝ)*base68 + (142639697444460087/276500000000000000000000000000000 : ℝ)*base70 + (538716913291039913/276500000000000000000000000000000 : ℝ)*base71 + (15345115506661/2765000000000000000000000000 : ℝ)*base74 + (1212179139899539913/276500000000000000000000000000000 : ℝ)*base75 + (140399625781960087/276500000000000000000000000000000 : ℝ)*base78 + (376002610045460087/276500000000000000000000000000000 : ℝ)*base80 + (6524980070661/2765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10165333/10000000000000000000000 : ℝ)*base89 + (10165333/10000000000000000000000 : ℝ)*base91 + (10165333/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1306_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6783/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6547/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9869/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1306_s2_0 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-258003471/1250000000 : ℝ)*x 0 + (5490011667/10000000000 : ℝ)*x 1 + (2587725633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258003471/1250000000 : ℝ)^2133 ≤ (2507814508671/20000000000000 : ℝ)^1621 := by
    have hnat : (258003471 : ℕ)^2133*20000000000000^1621 ≤ 2507814508671^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258003471 1250000000 2507814508671 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490011667/10000000000 : ℝ)^2133 ≤ (45427238303159/100000000000000 : ℝ)^1621 := by
    have hnat : (5490011667 : ℕ)^2133*100000000000000^1621 ≤ 45427238303159^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490011667 10000000000 45427238303159 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587725633/5000000000 : ℝ)^2133 ≤ (21016844571097/50000000000000 : ℝ)^1621 := by
    have hnat : (2587725633 : ℕ)^2133*50000000000000^1621 ≤ 21016844571097^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587725633 5000000000 21016844571097 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258003471/1250000000 : ℝ), (5490011667/10000000000 : ℝ), (2587725633/5000000000 : ℝ)] ![(2507814508671/20000000000000 : ℝ), (45427238303159/100000000000000 : ℝ), (21016844571097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258003471/1250000000 : ℝ)|^2133 ≤ (2507814508671/20000000000000 : ℝ)^1621
        have hw : |(-258003471/1250000000 : ℝ)|=(258003471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490011667/10000000000 : ℝ)|^2133 ≤ (45427238303159/100000000000000 : ℝ)^1621
        have hw : |(5490011667/10000000000 : ℝ)|=(5490011667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587725633/5000000000 : ℝ)|^2133 ≤ (21016844571097/50000000000000 : ℝ)^1621
        have hw : |(2587725633/5000000000 : ℝ)|=(2587725633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_1 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368542341/10000000000 : ℝ)*x 0 + (-89076003/400000000 : ℝ)*x 1 + (1293862747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368542341/10000000000 : ℝ)^2133 ≤ (44109316643121/100000000000000 : ℝ)^1621 := by
    have hnat : (5368542341 : ℕ)^2133*100000000000000^1621 ≤ 44109316643121^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368542341 10000000000 44109316643121 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89076003/400000000 : ℝ)^2133 ≤ (3464249292243/25000000000000 : ℝ)^1621 := by
    have hnat : (89076003 : ℕ)^2133*25000000000000^1621 ≤ 3464249292243^1621*400000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89076003 400000000 3464249292243 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293862747/2500000000 : ℝ)^2133 ≤ (42033686171199/100000000000000 : ℝ)^1621 := by
    have hnat : (1293862747 : ℕ)^2133*100000000000000^1621 ≤ 42033686171199^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293862747 2500000000 42033686171199 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368542341/10000000000 : ℝ), (-89076003/400000000 : ℝ), (1293862747/2500000000 : ℝ)] ![(44109316643121/100000000000000 : ℝ), (3464249292243/25000000000000 : ℝ), (42033686171199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368542341/10000000000 : ℝ)|^2133 ≤ (44109316643121/100000000000000 : ℝ)^1621
        have hw : |(5368542341/10000000000 : ℝ)|=(5368542341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89076003/400000000 : ℝ)|^2133 ≤ (3464249292243/25000000000000 : ℝ)^1621
        have hw : |(-89076003/400000000 : ℝ)|=(89076003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293862747/2500000000 : ℝ)|^2133 ≤ (42033686171199/100000000000000 : ℝ)^1621
        have hw : |(1293862747/2500000000 : ℝ)|=(1293862747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_2 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1073708387/2000000000 : ℝ)*x 0 + (5175451337/10000000000 : ℝ)*x 1 + (-556725039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073708387/2000000000 : ℝ)^2133 ≤ (22054656126847/50000000000000 : ℝ)^1621 := by
    have hnat : (1073708387 : ℕ)^2133*50000000000000^1621 ≤ 22054656126847^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073708387 2000000000 22054656126847 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175451337/10000000000 : ℝ)^2133 ≤ (21016844950487/50000000000000 : ℝ)^1621 := by
    have hnat : (5175451337 : ℕ)^2133*50000000000000^1621 ≤ 21016844950487^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175451337 10000000000 21016844950487 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556725039/2500000000 : ℝ)^2133 ≤ (13856997832197/100000000000000 : ℝ)^1621 := by
    have hnat : (556725039 : ℕ)^2133*100000000000000^1621 ≤ 13856997832197^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556725039 2500000000 13856997832197 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073708387/2000000000 : ℝ), (5175451337/10000000000 : ℝ), (-556725039/2500000000 : ℝ)] ![(22054656126847/50000000000000 : ℝ), (21016844950487/50000000000000 : ℝ), (13856997832197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073708387/2000000000 : ℝ)|^2133 ≤ (22054656126847/50000000000000 : ℝ)^1621
        have hw : |(1073708387/2000000000 : ℝ)|=(1073708387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175451337/10000000000 : ℝ)|^2133 ≤ (21016844950487/50000000000000 : ℝ)^1621
        have hw : |(5175451337/10000000000 : ℝ)|=(5175451337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556725039/2500000000 : ℝ)|^2133 ≤ (13856997832197/100000000000000 : ℝ)^1621
        have hw : |(-556725039/2500000000 : ℝ)|=(556725039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_3 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (865779131/2000000000 : ℝ)*x 0 + (4015463959/10000000000 : ℝ)*x 1 + (2332714187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865779131/2000000000 : ℝ)^2133 ≤ (33229608628071/100000000000000 : ℝ)^1621 := by
    have hnat : (865779131 : ℕ)^2133*100000000000000^1621 ≤ 33229608628071^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865779131 2000000000 33229608628071 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015463959/10000000000 : ℝ)^2133 ≤ (15050257127009/50000000000000 : ℝ)^1621 := by
    have hnat : (4015463959 : ℕ)^2133*50000000000000^1621 ≤ 15050257127009^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015463959 10000000000 15050257127009 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2332714187/5000000000 : ℝ)^2133 ≤ (7333975420103/20000000000000 : ℝ)^1621 := by
    have hnat : (2332714187 : ℕ)^2133*20000000000000^1621 ≤ 7333975420103^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2332714187 5000000000 7333975420103 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865779131/2000000000 : ℝ), (4015463959/10000000000 : ℝ), (2332714187/5000000000 : ℝ)] ![(33229608628071/100000000000000 : ℝ), (15050257127009/50000000000000 : ℝ), (7333975420103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865779131/2000000000 : ℝ)|^2133 ≤ (33229608628071/100000000000000 : ℝ)^1621
        have hw : |(865779131/2000000000 : ℝ)|=(865779131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015463959/10000000000 : ℝ)|^2133 ≤ (15050257127009/50000000000000 : ℝ)^1621
        have hw : |(4015463959/10000000000 : ℝ)|=(4015463959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2332714187/5000000000 : ℝ)|^2133 ≤ (7333975420103/20000000000000 : ℝ)^1621
        have hw : |(2332714187/5000000000 : ℝ)|=(2332714187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_4 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-41282099/200000000 : ℝ)*x 0 + (1035501093/2000000000 : ℝ)*x 1 + (68599231/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41282099/200000000 : ℝ)^2133 ≤ (626984476539/5000000000000 : ℝ)^1621 := by
    have hnat : (41282099 : ℕ)^2133*5000000000000^1621 ≤ 626984476539^1621*200000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41282099 200000000 626984476539 5000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035501093/2000000000 : ℝ)^2133 ≤ (42055643809401/100000000000000 : ℝ)^1621 := by
    have hnat : (1035501093 : ℕ)^2133*100000000000000^1621 ≤ 42055643809401^1621*2000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035501093 2000000000 42055643809401 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68599231/125000000 : ℝ)^2133 ≤ (45404666644089/100000000000000 : ℝ)^1621 := by
    have hnat : (68599231 : ℕ)^2133*100000000000000^1621 ≤ 45404666644089^1621*125000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68599231 125000000 45404666644089 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41282099/200000000 : ℝ), (1035501093/2000000000 : ℝ), (68599231/125000000 : ℝ)] ![(626984476539/5000000000000 : ℝ), (42055643809401/100000000000000 : ℝ), (45404666644089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41282099/200000000 : ℝ)|^2133 ≤ (626984476539/5000000000000 : ℝ)^1621
        have hw : |(-41282099/200000000 : ℝ)|=(41282099/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035501093/2000000000 : ℝ)|^2133 ≤ (42055643809401/100000000000000 : ℝ)^1621
        have hw : |(1035501093/2000000000 : ℝ)|=(1035501093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(68599231/125000000 : ℝ)|^2133 ≤ (45404666644089/100000000000000 : ℝ)^1621
        have hw : |(68599231/125000000 : ℝ)|=(68599231/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_5 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643894657/5000000000 : ℝ)*x 0 + (-1914412067/10000000000 : ℝ)*x 1 + (685992323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643894657/5000000000 : ℝ)^2133 ≤ (43238344782629/100000000000000 : ℝ)^1621 := by
    have hnat : (2643894657 : ℕ)^2133*100000000000000^1621 ≤ 43238344782629^1621*5000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643894657 5000000000 43238344782629 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1914412067/10000000000 : ℝ)^2133 ≤ (5678493708619/50000000000000 : ℝ)^1621 := by
    have hnat : (1914412067 : ℕ)^2133*50000000000000^1621 ≤ 5678493708619^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914412067 10000000000 5678493708619 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685992323/1250000000 : ℝ)^2133 ≤ (22702333888157/50000000000000 : ℝ)^1621 := by
    have hnat : (685992323 : ℕ)^2133*50000000000000^1621 ≤ 22702333888157^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685992323 1250000000 22702333888157 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643894657/5000000000 : ℝ), (-1914412067/10000000000 : ℝ), (685992323/1250000000 : ℝ)] ![(43238344782629/100000000000000 : ℝ), (5678493708619/50000000000000 : ℝ), (22702333888157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643894657/5000000000 : ℝ)|^2133 ≤ (43238344782629/100000000000000 : ℝ)^1621
        have hw : |(2643894657/5000000000 : ℝ)|=(2643894657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1914412067/10000000000 : ℝ)|^2133 ≤ (5678493708619/50000000000000 : ℝ)^1621
        have hw : |(-1914412067/10000000000 : ℝ)|=(1914412067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685992323/1250000000 : ℝ)|^2133 ≤ (22702333888157/50000000000000 : ℝ)^1621
        have hw : |(685992323/1250000000 : ℝ)|=(685992323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_6 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5287789447/10000000000 : ℝ)*x 0 + (5487938487/10000000000 : ℝ)*x 1 + (-1914412021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287789447/10000000000 : ℝ)^2133 ≤ (43238346213677/100000000000000 : ℝ)^1621 := by
    have hnat : (5287789447 : ℕ)^2133*100000000000000^1621 ≤ 43238346213677^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287789447 10000000000 43238346213677 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487938487/10000000000 : ℝ)^2133 ≤ (45404666720297/100000000000000 : ℝ)^1621 := by
    have hnat : (5487938487 : ℕ)^2133*100000000000000^1621 ≤ 45404666720297^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487938487 10000000000 45404666720297 100000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1914412021/10000000000 : ℝ)^2133 ≤ (2839246764539/25000000000000 : ℝ)^1621 := by
    have hnat : (1914412021 : ℕ)^2133*25000000000000^1621 ≤ 2839246764539^1621*10000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914412021 10000000000 2839246764539 25000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287789447/10000000000 : ℝ), (5487938487/10000000000 : ℝ), (-1914412021/10000000000 : ℝ)] ![(43238346213677/100000000000000 : ℝ), (45404666720297/100000000000000 : ℝ), (2839246764539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287789447/10000000000 : ℝ)|^2133 ≤ (43238346213677/100000000000000 : ℝ)^1621
        have hw : |(5287789447/10000000000 : ℝ)|=(5287789447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487938487/10000000000 : ℝ)|^2133 ≤ (45404666720297/100000000000000 : ℝ)^1621
        have hw : |(5487938487/10000000000 : ℝ)|=(5487938487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1914412021/10000000000 : ℝ)|^2133 ≤ (2839246764539/25000000000000 : ℝ)^1621
        have hw : |(-1914412021/10000000000 : ℝ)|=(1914412021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1306_s2_7 (p : ℝ) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ)) (x : Fin 3 → ℝ) :
    (541131763/1250000000 : ℝ)*x 0 + (466118193/1000000000 : ℝ)*x 1 + (1004938213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541131763/1250000000 : ℝ)^2133 ≤ (6646241819927/20000000000000 : ℝ)^1621 := by
    have hnat : (541131763 : ℕ)^2133*20000000000000^1621 ≤ 6646241819927^1621*1250000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541131763 1250000000 6646241819927 20000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466118193/1000000000 : ℝ)^2133 ≤ (18312982271831/50000000000000 : ℝ)^1621 := by
    have hnat : (466118193 : ℕ)^2133*50000000000000^1621 ≤ 18312982271831^1621*1000000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466118193 1000000000 18312982271831 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004938213/2500000000 : ℝ)^2133 ≤ (15071413171559/50000000000000 : ℝ)^1621 := by
    have hnat : (1004938213 : ℕ)^2133*50000000000000^1621 ≤ 15071413171559^1621*2500000000^2133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004938213 2500000000 15071413171559 50000000000000 2133 1621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2133/512 : ℝ)) 2133 1621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541131763/1250000000 : ℝ), (466118193/1000000000 : ℝ), (1004938213/2500000000 : ℝ)] ![(6646241819927/20000000000000 : ℝ), (18312982271831/50000000000000 : ℝ), (15071413171559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541131763/1250000000 : ℝ)|^2133 ≤ (6646241819927/20000000000000 : ℝ)^1621
        have hw : |(541131763/1250000000 : ℝ)|=(541131763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(466118193/1000000000 : ℝ)|^2133 ≤ (18312982271831/50000000000000 : ℝ)^1621
        have hw : |(466118193/1000000000 : ℝ)|=(466118193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004938213/2500000000 : ℝ)|^2133 ≤ (15071413171559/50000000000000 : ℝ)^1621
        have hw : |(1004938213/2500000000 : ℝ)|=(1004938213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1306_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9869/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4803/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8127/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9869/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9869/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6547/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9869/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9869/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6547/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9869/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9869/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6547/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6547/100000 : ℝ) ^ (4265/1024 : ℝ) ≤ (117157501566527/10000000000000000000 : ℝ) := by
    have hpowers : (6547/100000 : ℝ)^4265 ≤ (117157501566527/10000000000000000000 : ℝ)^1024 := by
      have hnat : (6547 : ℕ)^4265*10000000000000000000^1024 ≤ 117157501566527^1024*100000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6547 100000 117157501566527 10000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6547/100000 : ℝ)) (X := (117157501566527/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9869/50000 : ℝ) ^ (4265/1024 : ℝ) ≤ (23224162727488569/20000000000000000000 : ℝ) := by
    have hpowers : (9869/50000 : ℝ)^4265 ≤ (23224162727488569/20000000000000000000 : ℝ)^1024 := by
      have hnat : (9869 : ℕ)^4265*20000000000000000000^1024 ≤ 23224162727488569^1024*50000^4265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9869 50000 23224162727488569 20000000000000000000 4265 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9869/50000 : ℝ)) (X := (23224162727488569/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000117157501566527/5000000000000000000 : ℝ) ≤ (10000056257075521/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (5000117157501566527/5000000000000000000 : ℝ)^1024 ≤ (10000056257075521/10000000000000000 : ℝ)^4265 := by
      have hnat : (5000117157501566527 : ℕ)^1024*10000000000000000^4265 ≤ 10000056257075521^4265*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000117157501566527 5000000000000000000 10000056257075521 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000056257075521/10000000000000000 : ℝ)) (X := (5000117157501566527/5000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20023458477730621623/20000000000000000000 : ℝ) ≤ (2500703715804141/2500000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (20023458477730621623/20000000000000000000 : ℝ)^1024 ≤ (2500703715804141/2500000000000000 : ℝ)^4265 := by
      have hnat : (20023458477730621623 : ℕ)^1024*2500000000000000^4265 ≤ 2500703715804141^4265*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20023458477730621623 20000000000000000000 2500703715804141 2500000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500703715804141/2500000000000000 : ℝ)) (X := (20023458477730621623/20000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10023224162727488569/10000000000000000000 : ℝ) ≤ (10005573469357607/10000000000000000 : ℝ) ^ (4265/1024 : ℝ) := by
    have hpowers : (10023224162727488569/10000000000000000000 : ℝ)^1024 ≤ (10005573469357607/10000000000000000 : ℝ)^4265 := by
      have hnat : (10023224162727488569 : ℕ)^1024*10000000000000000^4265 ≤ 10005573469357607^4265*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10023224162727488569 10000000000000000000 10005573469357607 10000000000000000 1024 4265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005573469357607/10000000000000000 : ℝ)) (X := (10023224162727488569/10000000000000000000 : ℝ)) (by norm_num) 4265 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(117157501566527/10000000000000000000 : ℝ) ≤ ((131874620898272380469/131910000000000000000 : ℝ)+2*(2758606141043/1319100000000000 : ℝ)*(6547/100000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (131874620898272380469/131910000000000000000 : ℝ)+2*(2758606141043/1319100000000000 : ℝ)*(6547/100000 : ℝ)=(10000056257075521/10000000000000000 : ℝ) by norm_num, show 1+2*(117157501566527/10000000000000000000 : ℝ)=(5000117157501566527/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23224162727488569/20000000000000000000 : ℝ)+(117157501566527/10000000000000000000 : ℝ) ≤ ((131874620898272380469/131910000000000000000 : ℝ)+(2758606141043/1319100000000000 : ℝ)*((9869/50000 : ℝ)+(6547/100000 : ℝ)))^(4265/1024 : ℝ) := by
    rw [show (131874620898272380469/131910000000000000000 : ℝ)+(2758606141043/1319100000000000 : ℝ)*((9869/50000 : ℝ)+(6547/100000 : ℝ))=(2500703715804141/2500000000000000 : ℝ) by norm_num, show 1+(23224162727488569/20000000000000000000 : ℝ)+(117157501566527/10000000000000000000 : ℝ)=(20023458477730621623/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23224162727488569/20000000000000000000 : ℝ) ≤ ((131874620898272380469/131910000000000000000 : ℝ)+2*(2758606141043/1319100000000000 : ℝ)*(9869/50000 : ℝ))^(4265/1024 : ℝ) := by
    rw [show (131874620898272380469/131910000000000000000 : ℝ)+2*(2758606141043/1319100000000000 : ℝ)*(9869/50000 : ℝ)=(10005573469357607/10000000000000000 : ℝ) by norm_num, show 1+2*(23224162727488569/20000000000000000000 : ℝ)=(10023224162727488569/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (131874620898272380469/131910000000000000000 : ℝ)*(X 1 0+X 2 0)+(2758606141043/1319100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (6547/100000 : ℝ)) (hi := (9869/50000 : ℝ)) (c := (131874620898272380469/131910000000000000000 : ℝ)) (alpha := (2758606141043/1319100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (131874620898272380469/131910000000000000000 : ℝ)*(X 0 1+X 2 1)+(2758606141043/1319100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (6547/100000 : ℝ)) (hi := (9869/50000 : ℝ)) (c := (131874620898272380469/131910000000000000000 : ℝ)) (alpha := (2758606141043/1319100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (131874620898272380469/131910000000000000000 : ℝ)*(X 0 2+X 1 2)+(2758606141043/1319100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4265/1024 : ℝ)) (lo := (6547/100000 : ℝ)) (hi := (9869/50000 : ℝ)) (c := (131874620898272380469/131910000000000000000 : ℝ)) (alpha := (2758606141043/1319100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-258003471/1250000000 : ℝ)*X 0 0+(5490011667/10000000000 : ℝ)*X 0 1+(2587725633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368542341/10000000000 : ℝ)*X 1 0+(-89076003/400000000 : ℝ)*X 1 1+(1293862747/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1073708387/2000000000 : ℝ)*X 2 0+(5175451337/10000000000 : ℝ)*X 2 1+(-556725039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865779131/2000000000 : ℝ)*X 0 0+(4015463959/10000000000 : ℝ)*X 0 1+(2332714187/5000000000 : ℝ)*X 0 2+(865779131/2000000000 : ℝ)*X 1 0+(4015463959/10000000000 : ℝ)*X 1 1+(2332714187/5000000000 : ℝ)*X 1 2+(865779131/2000000000 : ℝ)*X 2 0+(4015463959/10000000000 : ℝ)*X 2 1+(2332714187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41282099/200000000 : ℝ)*X 0 0+(1035501093/2000000000 : ℝ)*X 0 1+(68599231/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643894657/5000000000 : ℝ)*X 1 0+(-1914412067/10000000000 : ℝ)*X 1 1+(685992323/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287789447/10000000000 : ℝ)*X 2 0+(5487938487/10000000000 : ℝ)*X 2 1+(-1914412021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((541131763/1250000000 : ℝ)*X 0 0+(466118193/1000000000 : ℝ)*X 0 1+(1004938213/2500000000 : ℝ)*X 0 2+(541131763/1250000000 : ℝ)*X 1 0+(466118193/1000000000 : ℝ)*X 1 1+(1004938213/2500000000 : ℝ)*X 1 2+(541131763/1250000000 : ℝ)*X 2 0+(466118193/1000000000 : ℝ)*X 2 1+(1004938213/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1306_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5260223131958760596197077337/1099250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1926104509/100000000000000 : ℝ)*(base19) + (50639153/4000000000000 : ℝ)*(base23) + (1408259/625000000000 : ℝ)*(lower2) + (314151847/50000000000000 : ℝ)*(upper3) + (172878129/100000000000000 : ℝ)*(upper5) + (1179409115050009/50000000000000 : ℝ)*(major0) + (1179409115050009/50000000000000 : ℝ)*(major1) + (1179409115050009/50000000000000 : ℝ)*(major2) + (3179054285139699/100000000000000 : ℝ)*(sp0) + (24836399701379/781250000000 : ℝ)*(sp1) + (635811964380439/20000000000000 : ℝ)*(sp2) + (153855820417101/10000000000000 : ℝ)*(sp3) + (6802741321/100000000000000 : ℝ)*(sp4) + (2126079817/12500000000000 : ℝ)*(sp7) + (769287606404773/50000000000000 : ℝ)*(f.failure) + (158953054394051/5000000000000 : ℝ)*(f.sum) + (216959131054907/32977500000000000000000000000 : ℝ)*base65 + (49783774139104574221/6595500000000000000000000000000000 : ℝ)*base67 + (70846418584165574221/6595500000000000000000000000000000 : ℝ)*base69 + (30237104208235574221/6595500000000000000000000000000000 : ℝ)*base71 + (11524438342769/16488750000000000000000000000 : ℝ)*base74 + (33336142464754574221/6595500000000000000000000000000000 : ℝ)*base75 + (83827172557734074221/6595500000000000000000000000000000 : ℝ)*base77 + (60980972844381074221/6595500000000000000000000000000000 : ℝ)*base79 + (31804072433207/32977500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (57706539/5000000000000000000000 : ℝ)*base90 + (57706539/5000000000000000000000 : ℝ)*base92 + (57706539/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (527216741335463927774615739/137406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6022807/781250000000 : ℝ)*(base19) + (511870199/50000000000000 : ℝ)*(base23) + (66805441/50000000000000 : ℝ)*(upper3) + (60973867/100000000000000 : ℝ)*(lower4) + (5643977/25000000000000 : ℝ)*(upper5) + (298770261983919/12500000000000 : ℝ)*(major0) + (298770261983919/12500000000000 : ℝ)*(major1) + (298770261983919/12500000000000 : ℝ)*(major2) + (792780919/10000000000000 : ℝ)*(sp1) + (2325345809/20000000000000 : ℝ)*(sp2) + (1610652167962411/50000000000000 : ℝ)*(sp4) + (201330977324771/6250000000000 : ℝ)*(sp5) + (3221291685455379/100000000000000 : ℝ)*(sp6) + (389754931980139/25000000000000 : ℝ)*(sp7) + (389754931980139/25000000000000 : ℝ)*(f.failure) + (1610652167962411/50000000000000 : ℝ)*(f.sum) + (718537358143/5496250000000000000000000000 : ℝ)*base65 + (2026575803182290663/549625000000000000000000000000000 : ℝ)*base68 + (6426342881828459337/549625000000000000000000000000000 : ℝ)*base69 + (338392523845709337/549625000000000000000000000000000 : ℝ)*base71 + (44729055234759/10992500000000000000000000000 : ℝ)*base74 + (3162748017147459337/549625000000000000000000000000000 : ℝ)*base75 + (1918058637218459337/549625000000000000000000000000000 : ℝ)*base77 + (2544598980858209337/549625000000000000000000000000000 : ℝ)*base79 + (44782158496707/21985000000000000000000000000 : ℝ)*base81 + (2791877/2500000000000000000000 : ℝ)*base90 + (2791877/2500000000000000000000 : ℝ)*base92 + (2791877/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1306_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9869/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6547/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1306_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1306_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1306_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1306_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1306_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4265/1024 : ℝ) ≤ p) (hpb : p ≤ (2133/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153311857/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4803/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8127/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1306_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
