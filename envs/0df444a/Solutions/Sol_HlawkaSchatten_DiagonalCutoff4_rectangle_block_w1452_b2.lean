-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1452_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:43.312989+00:00
-- url     : https://prove2.me/submissions/d4a8e3a6-41af-4855-9eaf-1832ae814668

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
theorem support_rectangle_w1452_s6_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-976309851/5000000000 : ℝ)*x 0 + (43256307/80000000 : ℝ)*x 1 + (163981039/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976309851/5000000000 : ℝ)^1103 ≤ (11918227541393/100000000000000 : ℝ)^847 := by
    have hnat : (976309851 : ℕ)^1103*100000000000000^847 ≤ 11918227541393^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976309851 5000000000 11918227541393 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43256307/80000000 : ℝ)^1103 ≤ (22450099150029/50000000000000 : ℝ)^847 := by
    have hnat : (43256307 : ℕ)^1103*50000000000000^847 ≤ 22450099150029^847*80000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43256307 80000000 22450099150029 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163981039/312500000 : ℝ)^1103 ≤ (43181574146819/100000000000000 : ℝ)^847 := by
    have hnat : (163981039 : ℕ)^1103*100000000000000^847 ≤ 43181574146819^847*312500000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163981039 312500000 43181574146819 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-976309851/5000000000 : ℝ), (43256307/80000000 : ℝ), (163981039/312500000 : ℝ)] ![(11918227541393/100000000000000 : ℝ), (22450099150029/50000000000000 : ℝ), (43181574146819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-976309851/5000000000 : ℝ)|^1103 ≤ (11918227541393/100000000000000 : ℝ)^847
        have hw : |(-976309851/5000000000 : ℝ)|=(976309851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43256307/80000000 : ℝ)|^1103 ≤ (22450099150029/50000000000000 : ℝ)^847
        have hw : |(43256307/80000000 : ℝ)|=(43256307/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163981039/312500000 : ℝ)|^1103 ≤ (43181574146819/100000000000000 : ℝ)^847
        have hw : |(163981039/312500000 : ℝ)|=(163981039/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346834347/10000000000 : ℝ)*x 0 + (-2033882219/10000000000 : ℝ)*x 1 + (2623696609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346834347/10000000000 : ℝ)^1103 ≤ (354002067497/800000000000 : ℝ)^847 := by
    have hnat : (5346834347 : ℕ)^1103*800000000000^847 ≤ 354002067497^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346834347 10000000000 354002067497 800000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033882219/10000000000 : ℝ)^1103 ≤ (2513633546131/20000000000000 : ℝ)^847 := by
    have hnat : (2033882219 : ℕ)^1103*20000000000000^847 ≤ 2513633546131^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033882219 10000000000 2513633546131 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623696609/5000000000 : ℝ)^1103 ≤ (43181573825329/100000000000000 : ℝ)^847 := by
    have hnat : (2623696609 : ℕ)^1103*100000000000000^847 ≤ 43181573825329^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623696609 5000000000 43181573825329 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346834347/10000000000 : ℝ), (-2033882219/10000000000 : ℝ), (2623696609/5000000000 : ℝ)] ![(354002067497/800000000000 : ℝ), (2513633546131/20000000000000 : ℝ), (43181573825329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346834347/10000000000 : ℝ)|^1103 ≤ (354002067497/800000000000 : ℝ)^847
        have hw : |(5346834347/10000000000 : ℝ)|=(5346834347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033882219/10000000000 : ℝ)|^1103 ≤ (2513633546131/20000000000000 : ℝ)^847
        have hw : |(-2033882219/10000000000 : ℝ)|=(2033882219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623696609/5000000000 : ℝ)|^1103 ≤ (43181573825329/100000000000000 : ℝ)^847
        have hw : |(2623696609/5000000000 : ℝ)|=(2623696609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336708601/2500000000 : ℝ)*x 0 + (1049478647/2000000000 : ℝ)*x 1 + (-1016941059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336708601/2500000000 : ℝ)^1103 ≤ (44250259051433/100000000000000 : ℝ)^847 := by
    have hnat : (1336708601 : ℕ)^1103*100000000000000^847 ≤ 44250259051433^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336708601 2500000000 44250259051433 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049478647/2000000000 : ℝ)^1103 ≤ (43181574007507/100000000000000 : ℝ)^847 := by
    have hnat : (1049478647 : ℕ)^1103*100000000000000^847 ≤ 43181574007507^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049478647 2000000000 43181574007507 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016941059/5000000000 : ℝ)^1103 ≤ (125681669179/1000000000000 : ℝ)^847 := by
    have hnat : (1016941059 : ℕ)^1103*1000000000000^847 ≤ 125681669179^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016941059 5000000000 125681669179 1000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336708601/2500000000 : ℝ), (1049478647/2000000000 : ℝ), (-1016941059/5000000000 : ℝ)] ![(44250259051433/100000000000000 : ℝ), (43181574007507/100000000000000 : ℝ), (125681669179/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336708601/2500000000 : ℝ)|^1103 ≤ (44250259051433/100000000000000 : ℝ)^847
        have hw : |(1336708601/2500000000 : ℝ)|=(1336708601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049478647/2000000000 : ℝ)|^1103 ≤ (43181574007507/100000000000000 : ℝ)^847
        have hw : |(1049478647/2000000000 : ℝ)|=(1049478647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016941059/5000000000 : ℝ)|^1103 ≤ (125681669179/1000000000000 : ℝ)^847
        have hw : |(-1016941059/5000000000 : ℝ)|=(1016941059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4298655157/10000000000 : ℝ)*x 0 + (4127657159/10000000000 : ℝ)*x 1 + (2237967829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298655157/10000000000 : ℝ)^1103 ≤ (6661006726243/20000000000000 : ℝ)^847 := by
    have hnat : (4298655157 : ℕ)^1103*20000000000000^847 ≤ 6661006726243^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298655157 10000000000 6661006726243 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127657159/10000000000 : ℝ)^1103 ≤ (1974388726283/6250000000000 : ℝ)^847 := by
    have hnat : (4127657159 : ℕ)^1103*6250000000000^847 ≤ 1974388726283^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127657159 10000000000 1974388726283 6250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237967829/5000000000 : ℝ)^1103 ≤ (7020949344723/20000000000000 : ℝ)^847 := by
    have hnat : (2237967829 : ℕ)^1103*20000000000000^847 ≤ 7020949344723^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237967829 5000000000 7020949344723 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298655157/10000000000 : ℝ), (4127657159/10000000000 : ℝ), (2237967829/5000000000 : ℝ)] ![(6661006726243/20000000000000 : ℝ), (1974388726283/6250000000000 : ℝ), (7020949344723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298655157/10000000000 : ℝ)|^1103 ≤ (6661006726243/20000000000000 : ℝ)^847
        have hw : |(4298655157/10000000000 : ℝ)|=(4298655157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127657159/10000000000 : ℝ)|^1103 ≤ (1974388726283/6250000000000 : ℝ)^847
        have hw : |(4127657159/10000000000 : ℝ)|=(4127657159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2237967829/5000000000 : ℝ)|^1103 ≤ (7020949344723/20000000000000 : ℝ)^847
        have hw : |(2237967829/5000000000 : ℝ)|=(2237967829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1952630661/10000000000 : ℝ)*x 0 + (1049593989/2000000000 : ℝ)*x 1 + (1351614701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952630661/10000000000 : ℝ)^1103 ≤ (744894665579/6250000000000 : ℝ)^847 := by
    have hnat : (1952630661 : ℕ)^1103*6250000000000^847 ≤ 744894665579^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952630661 10000000000 744894665579 6250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049593989/2000000000 : ℝ)^1103 ≤ (43187754337361/100000000000000 : ℝ)^847 := by
    have hnat : (1049593989 : ℕ)^1103*100000000000000^847 ≤ 43187754337361^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049593989 2000000000 43187754337361 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351614701/2500000000 : ℝ)^1103 ≤ (22446965499763/50000000000000 : ℝ)^847 := by
    have hnat : (1351614701 : ℕ)^1103*50000000000000^847 ≤ 22446965499763^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351614701 2500000000 22446965499763 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1952630661/10000000000 : ℝ), (1049593989/2000000000 : ℝ), (1351614701/2500000000 : ℝ)] ![(744894665579/6250000000000 : ℝ), (43187754337361/100000000000000 : ℝ), (22446965499763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1952630661/10000000000 : ℝ)|^1103 ≤ (744894665579/6250000000000 : ℝ)^847
        have hw : |(-1952630661/10000000000 : ℝ)|=(1952630661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049593989/2000000000 : ℝ)|^1103 ≤ (43187754337361/100000000000000 : ℝ)^847
        have hw : |(1049593989/2000000000 : ℝ)|=(1049593989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351614701/2500000000 : ℝ)|^1103 ≤ (22446965499763/50000000000000 : ℝ)^847
        have hw : |(1351614701/2500000000 : ℝ)|=(1351614701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (8488383/16000000 : ℝ)*x 0 + (-1874816639/10000000000 : ℝ)*x 1 + (5406458603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8488383/16000000 : ℝ)^1103 ≤ (21901251832759/50000000000000 : ℝ)^847 := by
    have hnat : (8488383 : ℕ)^1103*50000000000000^847 ≤ 21901251832759^847*16000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8488383 16000000 21901251832759 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1874816639/10000000000 : ℝ)^1103 ≤ (11303567496479/100000000000000 : ℝ)^847 := by
    have hnat : (1874816639 : ℕ)^1103*100000000000000^847 ≤ 11303567496479^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874816639 10000000000 11303567496479 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406458603/10000000000 : ℝ)^1103 ≤ (4489392882601/10000000000000 : ℝ)^847 := by
    have hnat : (5406458603 : ℕ)^1103*10000000000000^847 ≤ 4489392882601^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406458603 10000000000 4489392882601 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8488383/16000000 : ℝ), (-1874816639/10000000000 : ℝ), (5406458603/10000000000 : ℝ)] ![(21901251832759/50000000000000 : ℝ), (11303567496479/100000000000000 : ℝ), (4489392882601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8488383/16000000 : ℝ)|^1103 ≤ (21901251832759/50000000000000 : ℝ)^847
        have hw : |(8488383/16000000 : ℝ)|=(8488383/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1874816639/10000000000 : ℝ)|^1103 ≤ (11303567496479/100000000000000 : ℝ)^847
        have hw : |(-1874816639/10000000000 : ℝ)|=(1874816639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406458603/10000000000 : ℝ)|^1103 ≤ (4489392882601/10000000000000 : ℝ)^847
        have hw : |(5406458603/10000000000 : ℝ)|=(5406458603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652620003/5000000000 : ℝ)*x 0 + (216258309/400000000 : ℝ)*x 1 + (-234352123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652620003/5000000000 : ℝ)^1103 ≤ (2190125522499/5000000000000 : ℝ)^847 := by
    have hnat : (2652620003 : ℕ)^1103*5000000000000^847 ≤ 2190125522499^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652620003 5000000000 2190125522499 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216258309/400000000 : ℝ)^1103 ≤ (8978783866349/20000000000000 : ℝ)^847 := by
    have hnat : (216258309 : ℕ)^1103*20000000000000^847 ≤ 8978783866349^847*400000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216258309 400000000 8978783866349 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234352123/1250000000 : ℝ)^1103 ≤ (11303570205223/100000000000000 : ℝ)^847 := by
    have hnat : (234352123 : ℕ)^1103*100000000000000^847 ≤ 11303570205223^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234352123 1250000000 11303570205223 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652620003/5000000000 : ℝ), (216258309/400000000 : ℝ), (-234352123/1250000000 : ℝ)] ![(2190125522499/5000000000000 : ℝ), (8978783866349/20000000000000 : ℝ), (11303570205223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652620003/5000000000 : ℝ)|^1103 ≤ (2190125522499/5000000000000 : ℝ)^847
        have hw : |(2652620003/5000000000 : ℝ)|=(2652620003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216258309/400000000 : ℝ)|^1103 ≤ (8978783866349/20000000000000 : ℝ)^847
        have hw : |(216258309/400000000 : ℝ)|=(216258309/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234352123/1250000000 : ℝ)|^1103 ≤ (11303570205223/100000000000000 : ℝ)^847
        have hw : |(-234352123/1250000000 : ℝ)|=(234352123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s6_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4298679649/10000000000 : ℝ)*x 0 + (279667281/625000000 : ℝ)*x 1 + (4128922623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298679649/10000000000 : ℝ)^1103 ≤ (33305280743307/100000000000000 : ℝ)^847 := by
    have hnat : (4298679649 : ℕ)^1103*100000000000000^847 ≤ 33305280743307^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298679649 10000000000 33305280743307 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279667281/625000000 : ℝ)^1103 ≤ (4386485854197/12500000000000 : ℝ)^847 := by
    have hnat : (279667281 : ℕ)^1103*12500000000000^847 ≤ 4386485854197^847*625000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279667281 625000000 4386485854197 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128922623/10000000000 : ℝ)^1103 ≤ (3160283240701/10000000000000 : ℝ)^847 := by
    have hnat : (4128922623 : ℕ)^1103*10000000000000^847 ≤ 3160283240701^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128922623 10000000000 3160283240701 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298679649/10000000000 : ℝ), (279667281/625000000 : ℝ), (4128922623/10000000000 : ℝ)] ![(33305280743307/100000000000000 : ℝ), (4386485854197/12500000000000 : ℝ), (3160283240701/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298679649/10000000000 : ℝ)|^1103 ≤ (33305280743307/100000000000000 : ℝ)^847
        have hw : |(4298679649/10000000000 : ℝ)|=(4298679649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(279667281/625000000 : ℝ)|^1103 ≤ (4386485854197/12500000000000 : ℝ)^847
        have hw : |(279667281/625000000 : ℝ)|=(279667281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128922623/10000000000 : ℝ)|^1103 ≤ (3160283240701/10000000000000 : ℝ)^847
        have hw : |(4128922623/10000000000 : ℝ)|=(4128922623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5693/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14769/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3693/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3693/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11383/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (8604295057763991/100000000000000000000 : ℝ) := by
    have hpowers : (11383/100000 : ℝ)^4411 ≤ (8604295057763991/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11383 : ℕ)^4411*100000000000000000000^1024 ≤ 8604295057763991^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11383 100000 8604295057763991 100000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11383/100000 : ℝ)) (X := (8604295057763991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3693/25000 : ℝ) ^ (4411/1024 : ℝ) ≤ (26440060771202507/100000000000000000000 : ℝ) := by
    have hpowers : (3693/25000 : ℝ)^4411 ≤ (26440060771202507/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3693 : ℕ)^4411*100000000000000000000^1024 ≤ 26440060771202507^1024*25000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3693 25000 26440060771202507 100000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3693/25000 : ℝ)) (X := (26440060771202507/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008604295057763991/50000000000000000000 : ℝ) ≤ (5000199732851583/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50008604295057763991/50000000000000000000 : ℝ)^1024 ≤ (5000199732851583/5000000000000000 : ℝ)^4411 := by
      have hnat : (50008604295057763991 : ℕ)^1024*5000000000000000^4411 ≤ 5000199732851583^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008604295057763991 50000000000000000000 5000199732851583 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199732851583/5000000000000000 : ℝ)) (X := (50008604295057763991/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017522177914483249/50000000000000000000 : ℝ) ≤ (5000406717220321/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50017522177914483249/50000000000000000000 : ℝ)^1024 ≤ (5000406717220321/5000000000000000 : ℝ)^4411 := by
      have hnat : (50017522177914483249 : ℕ)^1024*5000000000000000^4411 ≤ 5000406717220321^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017522177914483249 50000000000000000000 5000406717220321 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000406717220321/5000000000000000 : ℝ)) (X := (50017522177914483249/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026440060771202507/50000000000000000000 : ℝ) ≤ (5000613701589059/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (50026440060771202507/50000000000000000000 : ℝ)^1024 ≤ (5000613701589059/5000000000000000 : ℝ)^4411 := by
      have hnat : (50026440060771202507 : ℕ)^1024*5000000000000000^4411 ≤ 5000613701589059^4411*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026440060771202507 50000000000000000000 5000613701589059 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000613701589059/5000000000000000 : ℝ)) (X := (50026440060771202507/50000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8604295057763991/100000000000000000000 : ℝ) ≤ ((16940964688495325479/16945000000000000000 : ℝ)+2*(103492184369/84725000000000 : ℝ)*(11383/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (16940964688495325479/16945000000000000000 : ℝ)+2*(103492184369/84725000000000 : ℝ)*(11383/100000 : ℝ)=(5000199732851583/5000000000000000 : ℝ) by norm_num, show 1+2*(8604295057763991/100000000000000000000 : ℝ)=(50008604295057763991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26440060771202507/100000000000000000000 : ℝ)+(8604295057763991/100000000000000000000 : ℝ) ≤ ((16940964688495325479/16945000000000000000 : ℝ)+(103492184369/84725000000000 : ℝ)*((3693/25000 : ℝ)+(11383/100000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (16940964688495325479/16945000000000000000 : ℝ)+(103492184369/84725000000000 : ℝ)*((3693/25000 : ℝ)+(11383/100000 : ℝ))=(5000406717220321/5000000000000000 : ℝ) by norm_num, show 1+(26440060771202507/100000000000000000000 : ℝ)+(8604295057763991/100000000000000000000 : ℝ)=(50017522177914483249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26440060771202507/100000000000000000000 : ℝ) ≤ ((16940964688495325479/16945000000000000000 : ℝ)+2*(103492184369/84725000000000 : ℝ)*(3693/25000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (16940964688495325479/16945000000000000000 : ℝ)+2*(103492184369/84725000000000 : ℝ)*(3693/25000 : ℝ)=(5000613701589059/5000000000000000 : ℝ) by norm_num, show 1+2*(26440060771202507/100000000000000000000 : ℝ)=(50026440060771202507/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16940964688495325479/16945000000000000000 : ℝ)*(X 1 0+X 2 0)+(103492184369/84725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (16940964688495325479/16945000000000000000 : ℝ)) (alpha := (103492184369/84725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16940964688495325479/16945000000000000000 : ℝ)*(X 0 1+X 2 1)+(103492184369/84725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (16940964688495325479/16945000000000000000 : ℝ)) (alpha := (103492184369/84725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16940964688495325479/16945000000000000000 : ℝ)*(X 0 2+X 1 2)+(103492184369/84725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (3693/25000 : ℝ)) (c := (16940964688495325479/16945000000000000000 : ℝ)) (alpha := (103492184369/84725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-976309851/5000000000 : ℝ)*X 0 0+(43256307/80000000 : ℝ)*X 0 1+(163981039/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346834347/10000000000 : ℝ)*X 1 0+(-2033882219/10000000000 : ℝ)*X 1 1+(2623696609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336708601/2500000000 : ℝ)*X 2 0+(1049478647/2000000000 : ℝ)*X 2 1+(-1016941059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298655157/10000000000 : ℝ)*X 0 0+(4127657159/10000000000 : ℝ)*X 0 1+(2237967829/5000000000 : ℝ)*X 0 2+(4298655157/10000000000 : ℝ)*X 1 0+(4127657159/10000000000 : ℝ)*X 1 1+(2237967829/5000000000 : ℝ)*X 1 2+(4298655157/10000000000 : ℝ)*X 2 0+(4127657159/10000000000 : ℝ)*X 2 1+(2237967829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1952630661/10000000000 : ℝ)*X 0 0+(1049593989/2000000000 : ℝ)*X 0 1+(1351614701/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8488383/16000000 : ℝ)*X 1 0+(-1874816639/10000000000 : ℝ)*X 1 1+(5406458603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652620003/5000000000 : ℝ)*X 2 0+(216258309/400000000 : ℝ)*X 2 1+(-234352123/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298679649/10000000000 : ℝ)*X 0 0+(279667281/625000000 : ℝ)*X 0 1+(4128922623/10000000000 : ℝ)*X 0 2+(4298679649/10000000000 : ℝ)*X 1 0+(279667281/625000000 : ℝ)*X 1 1+(4128922623/10000000000 : ℝ)*X 1 2+(4298679649/10000000000 : ℝ)*X 2 0+(279667281/625000000 : ℝ)*X 2 1+(4128922623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55673922255931428475315347/6619140625000000000000000000000 : ℝ) := by norm_num
    linear_combination (805189083/50000000000000 : ℝ)*(base19) + (322414617/20000000000000 : ℝ)*(base23) + (17399167/50000000000000 : ℝ)*(lower2) + (74907157/50000000000000 : ℝ)*(upper3) + (242537467/100000000000000 : ℝ)*(upper5) + (285476944199349/6250000000000 : ℝ)*(major0) + (285476944199349/6250000000000 : ℝ)*(major1) + (913526221437917/20000000000000 : ℝ)*(major2) + (6263925193959493/100000000000000 : ℝ)*(sp0) + (1252792219826731/20000000000000 : ℝ)*(sp1) + (6263961097438737/100000000000000 : ℝ)*(sp2) + (717820666201083/25000000000000 : ℝ)*(sp3) + (4689444041/12500000000000 : ℝ)*(sp4) + (4139923669/25000000000000 : ℝ)*(sp7) + (44864050382797/1562500000000 : ℝ)*(f.failure) + (6263962709511821/100000000000000 : ℝ)*(f.sum) + (3152594138351/2118125000000000000000000000 : ℝ)*base66 + (250371066458368079/105906250000000000000000000000000 : ℝ)*base68 + (154107731355372757/338900000000000000000000000000000 : ℝ)*base70 + (341022920591055579/105906250000000000000000000000000 : ℝ)*base72 + (65597013375867/16945000000000000000000000000 : ℝ)*base73 + (5834067919980027243/338900000000000000000000000000000 : ℝ)*base75 + (902301649011829/105906250000000000000000000000000 : ℝ)*base78 + (261770119451730579/105906250000000000000000000000000 : ℝ)*base80 + (29809608780463/8472500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (52993/9765625000000000000 : ℝ)*base90 + (52993/9765625000000000000 : ℝ)*base92 + (602597/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (245274725549004308483680839/26476562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (33019197/1562500000000 : ℝ)*(base19) + (1534811/48828125000 : ℝ)*(base23) + (8409039/1250000000000 : ℝ)*(lower1) + (209138979/100000000000000 : ℝ)*(lower4) + (394031541/100000000000000 : ℝ)*(upper5) + (35944447733009/781250000000 : ℝ)*(major0) + (35944447733009/781250000000 : ℝ)*(major1) + (35944447733009/781250000000 : ℝ)*(major2) + (1927813129/50000000000000 : ℝ)*(sp0) + (1827114353/12500000000000 : ℝ)*(sp1) + (1577392124025611/25000000000000 : ℝ)*(sp4) + (630955562158527/10000000000000 : ℝ)*(sp5) + (3154784604217887/50000000000000 : ℝ)*(sp6) + (1446102979563409/50000000000000 : ℝ)*(sp7) + (1446102979563409/50000000000000 : ℝ)*(f.failure) + (3154786175864351/50000000000000 : ℝ)*(f.sum) + (15054835298931/8472500000000000000000000000 : ℝ)*base65 + (394651593697543003/26476562500000000000000000000000 : ℝ)*base68 + (370360949859449253/26476562500000000000000000000000 : ℝ)*base70 + (10620563873170907/6619140625000000000000000000000 : ℝ)*base72 + (52619186095919/8472500000000000000000000000 : ℝ)*base74 + (184391718037138689/13238281250000000000000000000000 : ℝ)*base76 + (266095583549511753/26476562500000000000000000000000 : ℝ)*base78 + (53015241833863247/26476562500000000000000000000000 : ℝ)*base79 + (24951138089879/8472500000000000000000000000 : ℝ)*base82 + (4107279/312500000000000000000 : ℝ)*base89 + (4107279/312500000000000000000 : ℝ)*base91 + (4107279/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1452_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1452_s7_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1952623181/10000000000 : ℝ)*x 0 + (5407018909/10000000000 : ℝ)*x 1 + (5247410311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952623181/10000000000 : ℝ)^1103 ≤ (11918255194291/100000000000000 : ℝ)^847 := by
    have hnat : (1952623181 : ℕ)^1103*100000000000000^847 ≤ 11918255194291^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952623181 10000000000 11918255194291 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407018909/10000000000 : ℝ)^1103 ≤ (22449993898747/50000000000000 : ℝ)^847 := by
    have hnat : (5407018909 : ℕ)^1103*50000000000000^847 ≤ 22449993898747^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407018909 10000000000 22449993898747 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247410311/10000000000 : ℝ)^1103 ≤ (43181757000019/100000000000000 : ℝ)^847 := by
    have hnat : (5247410311 : ℕ)^1103*100000000000000^847 ≤ 43181757000019^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247410311 10000000000 43181757000019 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1952623181/10000000000 : ℝ), (5407018909/10000000000 : ℝ), (5247410311/10000000000 : ℝ)] ![(11918255194291/100000000000000 : ℝ), (22449993898747/50000000000000 : ℝ), (43181757000019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1952623181/10000000000 : ℝ)|^1103 ≤ (11918255194291/100000000000000 : ℝ)^847
        have hw : |(-1952623181/10000000000 : ℝ)|=(1952623181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407018909/10000000000 : ℝ)|^1103 ≤ (22449993898747/50000000000000 : ℝ)^847
        have hw : |(5407018909/10000000000 : ℝ)|=(5407018909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247410311/10000000000 : ℝ)|^1103 ≤ (43181757000019/100000000000000 : ℝ)^847
        have hw : |(5247410311/10000000000 : ℝ)|=(5247410311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346828321/10000000000 : ℝ)*x 0 + (-2033865783/10000000000 : ℝ)*x 1 + (262370581/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346828321/10000000000 : ℝ)^1103 ≤ (8850038698589/20000000000000 : ℝ)^847 := by
    have hnat : (5346828321 : ℕ)^1103*20000000000000^847 ≤ 8850038698589^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346828321 10000000000 8850038698589 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033865783/10000000000 : ℝ)^1103 ≤ (392751108407/3125000000000 : ℝ)^847 := by
    have hnat : (2033865783 : ℕ)^1103*3125000000000^847 ≤ 392751108407^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033865783 10000000000 392751108407 3125000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262370581/500000000 : ℝ)^1103 ≤ (21590885513869/50000000000000 : ℝ)^847 := by
    have hnat : (262370581 : ℕ)^1103*50000000000000^847 ≤ 21590885513869^847*500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262370581 500000000 21590885513869 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346828321/10000000000 : ℝ), (-2033865783/10000000000 : ℝ), (262370581/500000000 : ℝ)] ![(8850038698589/20000000000000 : ℝ), (392751108407/3125000000000 : ℝ), (21590885513869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346828321/10000000000 : ℝ)|^1103 ≤ (8850038698589/20000000000000 : ℝ)^847
        have hw : |(5346828321/10000000000 : ℝ)|=(5346828321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033865783/10000000000 : ℝ)|^1103 ≤ (392751108407/3125000000000 : ℝ)^847
        have hw : |(-2033865783/10000000000 : ℝ)|=(2033865783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262370581/500000000 : ℝ)|^1103 ≤ (21590885513869/50000000000000 : ℝ)^847
        have hw : |(262370581/500000000 : ℝ)|=(262370581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346825167/10000000000 : ℝ)*x 0 + (2623708811/5000000000 : ℝ)*x 1 + (-1016931007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346825167/10000000000 : ℝ)^1103 ≤ (2212507975063/5000000000000 : ℝ)^847 := by
    have hnat : (5346825167 : ℕ)^1103*5000000000000^847 ≤ 2212507975063^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346825167 10000000000 2212507975063 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623708811/5000000000 : ℝ)^1103 ≤ (269886470921/625000000000 : ℝ)^847 := by
    have hnat : (2623708811 : ℕ)^1103*625000000000^847 ≤ 269886470921^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623708811 5000000000 269886470921 625000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016931007/5000000000 : ℝ)^1103 ≤ (6284002569833/50000000000000 : ℝ)^847 := by
    have hnat : (1016931007 : ℕ)^1103*50000000000000^847 ≤ 6284002569833^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016931007 5000000000 6284002569833 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346825167/10000000000 : ℝ), (2623708811/5000000000 : ℝ), (-1016931007/5000000000 : ℝ)] ![(2212507975063/5000000000000 : ℝ), (269886470921/625000000000 : ℝ), (6284002569833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346825167/10000000000 : ℝ)|^1103 ≤ (2212507975063/5000000000000 : ℝ)^847
        have hw : |(5346825167/10000000000 : ℝ)|=(5346825167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623708811/5000000000 : ℝ)|^1103 ≤ (269886470921/625000000000 : ℝ)^847
        have hw : |(2623708811/5000000000 : ℝ)|=(2623708811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016931007/5000000000 : ℝ)|^1103 ≤ (6284002569833/50000000000000 : ℝ)^847
        have hw : |(-1016931007/5000000000 : ℝ)|=(1016931007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4298657249/10000000000 : ℝ)*x 0 + (2063850611/5000000000 : ℝ)*x 1 + (895178119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298657249/10000000000 : ℝ)^1103 ≤ (16652527369219/50000000000000 : ℝ)^847 := by
    have hnat : (4298657249 : ℕ)^1103*50000000000000^847 ≤ 16652527369219^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298657249 10000000000 16652527369219 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063850611/5000000000 : ℝ)^1103 ≤ (31590658773567/100000000000000 : ℝ)^847 := by
    have hnat : (2063850611 : ℕ)^1103*100000000000000^847 ≤ 31590658773567^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063850611 5000000000 31590658773567 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895178119/2000000000 : ℝ)^1103 ≤ (8776071618469/25000000000000 : ℝ)^847 := by
    have hnat : (895178119 : ℕ)^1103*25000000000000^847 ≤ 8776071618469^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895178119 2000000000 8776071618469 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298657249/10000000000 : ℝ), (2063850611/5000000000 : ℝ), (895178119/2000000000 : ℝ)] ![(16652527369219/50000000000000 : ℝ), (31590658773567/100000000000000 : ℝ), (8776071618469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298657249/10000000000 : ℝ)|^1103 ≤ (16652527369219/50000000000000 : ℝ)^847
        have hw : |(4298657249/10000000000 : ℝ)|=(4298657249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063850611/5000000000 : ℝ)|^1103 ≤ (31590658773567/100000000000000 : ℝ)^847
        have hw : |(2063850611/5000000000 : ℝ)|=(2063850611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895178119/2000000000 : ℝ)|^1103 ≤ (8776071618469/25000000000000 : ℝ)^847
        have hw : |(895178119/2000000000 : ℝ)|=(895178119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1952632723/10000000000 : ℝ)*x 0 + (5247989503/10000000000 : ℝ)*x 1 + (1081287581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952632723/10000000000 : ℝ)^1103 ≤ (11918331039137/100000000000000 : ℝ)^847 := by
    have hnat : (1952632723 : ℕ)^1103*100000000000000^847 ≤ 11918331039137^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952632723 10000000000 11918331039137 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247989503/10000000000 : ℝ)^1103 ≤ (337405968241/781250000000 : ℝ)^847 := by
    have hnat : (5247989503 : ℕ)^1103*781250000000^847 ≤ 337405968241^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247989503 10000000000 337405968241 781250000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081287581/2000000000 : ℝ)^1103 ≤ (44893705008033/100000000000000 : ℝ)^847 := by
    have hnat : (1081287581 : ℕ)^1103*100000000000000^847 ≤ 44893705008033^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081287581 2000000000 44893705008033 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1952632723/10000000000 : ℝ), (5247989503/10000000000 : ℝ), (1081287581/2000000000 : ℝ)] ![(11918331039137/100000000000000 : ℝ), (337405968241/781250000000 : ℝ), (44893705008033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1952632723/10000000000 : ℝ)|^1103 ≤ (11918331039137/100000000000000 : ℝ)^847
        have hw : |(-1952632723/10000000000 : ℝ)|=(1952632723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247989503/10000000000 : ℝ)|^1103 ≤ (337405968241/781250000000 : ℝ)^847
        have hw : |(5247989503/10000000000 : ℝ)|=(5247989503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081287581/2000000000 : ℝ)|^1103 ≤ (44893705008033/100000000000000 : ℝ)^847
        have hw : |(1081287581/2000000000 : ℝ)|=(1081287581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (132631113/250000000 : ℝ)*x 0 + (-1874838093/10000000000 : ℝ)*x 1 + (5406437909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132631113/250000000 : ℝ)^1103 ≤ (21901279492079/50000000000000 : ℝ)^847 := by
    have hnat : (132631113 : ℕ)^1103*50000000000000^847 ≤ 21901279492079^847*250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132631113 250000000 21901279492079 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1874838093/10000000000 : ℝ)^1103 ≤ (11303735941377/100000000000000 : ℝ)^847 := by
    have hnat : (1874838093 : ℕ)^1103*100000000000000^847 ≤ 11303735941377^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874838093 10000000000 11303735941377 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406437909/10000000000 : ℝ)^1103 ≤ (44893705051287/100000000000000 : ℝ)^847 := by
    have hnat : (5406437909 : ℕ)^1103*100000000000000^847 ≤ 44893705051287^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406437909 10000000000 44893705051287 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132631113/250000000 : ℝ), (-1874838093/10000000000 : ℝ), (5406437909/10000000000 : ℝ)] ![(21901279492079/50000000000000 : ℝ), (11303735941377/100000000000000 : ℝ), (44893705051287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132631113/250000000 : ℝ)|^1103 ≤ (21901279492079/50000000000000 : ℝ)^847
        have hw : |(132631113/250000000 : ℝ)|=(132631113/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1874838093/10000000000 : ℝ)|^1103 ≤ (11303735941377/100000000000000 : ℝ)^847
        have hw : |(-1874838093/10000000000 : ℝ)|=(1874838093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406437909/10000000000 : ℝ)|^1103 ≤ (44893705051287/100000000000000 : ℝ)^847
        have hw : |(5406437909/10000000000 : ℝ)|=(5406437909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305244501/10000000000 : ℝ)*x 0 + (2703218957/5000000000 : ℝ)*x 1 + (-937419057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305244501/10000000000 : ℝ)^1103 ≤ (1368829961871/3125000000000 : ℝ)^847 := by
    have hnat : (5305244501 : ℕ)^1103*3125000000000^847 ≤ 1368829961871^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305244501 10000000000 1368829961871 3125000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703218957/5000000000 : ℝ)^1103 ≤ (8978741021071/20000000000000 : ℝ)^847 := by
    have hnat : (2703218957 : ℕ)^1103*20000000000000^847 ≤ 8978741021071^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703218957 5000000000 8978741021071 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937419057/5000000000 : ℝ)^1103 ≤ (5651868053129/50000000000000 : ℝ)^847 := by
    have hnat : (937419057 : ℕ)^1103*50000000000000^847 ≤ 5651868053129^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937419057 5000000000 5651868053129 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305244501/10000000000 : ℝ), (2703218957/5000000000 : ℝ), (-937419057/5000000000 : ℝ)] ![(1368829961871/3125000000000 : ℝ), (8978741021071/20000000000000 : ℝ), (5651868053129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305244501/10000000000 : ℝ)|^1103 ≤ (1368829961871/3125000000000 : ℝ)^847
        have hw : |(5305244501/10000000000 : ℝ)|=(5305244501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703218957/5000000000 : ℝ)|^1103 ≤ (8978741021071/20000000000000 : ℝ)^847
        have hw : |(2703218957/5000000000 : ℝ)|=(2703218957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937419057/5000000000 : ℝ)|^1103 ≤ (5651868053129/50000000000000 : ℝ)^847
        have hw : |(-937419057/5000000000 : ℝ)|=(937419057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1074670197/2500000000 : ℝ)*x 0 + (4474633277/10000000000 : ℝ)*x 1 + (4128965753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074670197/2500000000 : ℝ)^1103 ≤ (1665264611763/5000000000000 : ℝ)^847 := by
    have hnat : (1074670197 : ℕ)^1103*5000000000000^847 ≤ 1665264611763^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074670197 2500000000 1665264611763 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474633277/10000000000 : ℝ)^1103 ≤ (3509144545499/10000000000000 : ℝ)^847 := by
    have hnat : (4474633277 : ℕ)^1103*10000000000000^847 ≤ 3509144545499^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474633277 10000000000 3509144545499 10000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128965753/10000000000 : ℝ)^1103 ≤ (15801631150567/50000000000000 : ℝ)^847 := by
    have hnat : (4128965753 : ℕ)^1103*50000000000000^847 ≤ 15801631150567^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128965753 10000000000 15801631150567 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074670197/2500000000 : ℝ), (4474633277/10000000000 : ℝ), (4128965753/10000000000 : ℝ)] ![(1665264611763/5000000000000 : ℝ), (3509144545499/10000000000000 : ℝ), (15801631150567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074670197/2500000000 : ℝ)|^1103 ≤ (1665264611763/5000000000000 : ℝ)^847
        have hw : |(1074670197/2500000000 : ℝ)|=(1074670197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4474633277/10000000000 : ℝ)|^1103 ≤ (3509144545499/10000000000000 : ℝ)^847
        have hw : |(4474633277/10000000000 : ℝ)|=(4474633277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128965753/10000000000 : ℝ)|^1103 ≤ (15801631150567/50000000000000 : ℝ)^847
        have hw : |(4128965753/10000000000 : ℝ)|=(4128965753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_s7_8 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1049021977/1250000000 : ℝ)*x 0 + (1248493577/5000000000 : ℝ)*x 1 + (-842996723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049021977/1250000000 : ℝ)^1103 ≤ (9948925836403/12500000000000 : ℝ)^847 := by
    have hnat : (1049021977 : ℕ)^1103*12500000000000^847 ≤ 9948925836403^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049021977 1250000000 9948925836403 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1248493577/5000000000 : ℝ)^1103 ≤ (8208418344497/50000000000000 : ℝ)^847 := by
    have hnat : (1248493577 : ℕ)^1103*50000000000000^847 ≤ 8208418344497^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248493577 5000000000 8208418344497 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842996723/10000000000 : ℝ)^1103 ≤ (3991756606667/100000000000000 : ℝ)^847 := by
    have hnat : (842996723 : ℕ)^1103*100000000000000^847 ≤ 3991756606667^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842996723 10000000000 3991756606667 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049021977/1250000000 : ℝ), (1248493577/5000000000 : ℝ), (-842996723/10000000000 : ℝ)] ![(9948925836403/12500000000000 : ℝ), (8208418344497/50000000000000 : ℝ), (3991756606667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049021977/1250000000 : ℝ)|^1103 ≤ (9948925836403/12500000000000 : ℝ)^847
        have hw : |(1049021977/1250000000 : ℝ)|=(1049021977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1248493577/5000000000 : ℝ)|^1103 ≤ (8208418344497/50000000000000 : ℝ)^847
        have hw : |(1248493577/5000000000 : ℝ)|=(1248493577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-842996723/10000000000 : ℝ)|^1103 ≤ (3991756606667/100000000000000 : ℝ)^847
        have hw : |(-842996723/10000000000 : ℝ)|=(842996723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11387/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5693/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5693/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5693/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5693/50000 : ℝ) ^ (4411/1024 : ℝ) ≤ (4307033784795253/50000000000000000000 : ℝ) := by
    have hpowers : (5693/50000 : ℝ)^4411 ≤ (4307033784795253/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5693 : ℕ)^4411*50000000000000000000^1024 ≤ 4307033784795253^1024*50000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5693 50000 4307033784795253 50000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5693/50000 : ℝ)) (X := (4307033784795253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (5283387645179501/20000000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^4411 ≤ (5283387645179501/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14769 : ℕ)^4411*20000000000000000000^1024 ≤ 5283387645179501^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 5283387645179501 20000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (5283387645179501/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004307033784795253/25000000000000000000 : ℝ) ≤ (5000199959687431/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (25004307033784795253/25000000000000000000 : ℝ)^1024 ≤ (5000199959687431/5000000000000000 : ℝ)^4411 := by
      have hnat : (25004307033784795253 : ℕ)^1024*5000000000000000^4411 ≤ 5000199959687431^4411*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004307033784795253 25000000000000000000 5000199959687431 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000199959687431/5000000000000000 : ℝ)) (X := (25004307033784795253/25000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035031005795488011/100000000000000000000 : ℝ) ≤ (10000813124607099/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (100035031005795488011/100000000000000000000 : ℝ)^1024 ≤ (10000813124607099/10000000000000000 : ℝ)^4411 := by
      have hnat : (100035031005795488011 : ℕ)^1024*10000000000000000^4411 ≤ 10000813124607099^4411*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035031005795488011 100000000000000000000 10000813124607099 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000813124607099/10000000000000000 : ℝ)) (X := (100035031005795488011/100000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005283387645179501/10000000000000000000 : ℝ) ≤ (1250153291229917/1250000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (10005283387645179501/10000000000000000000 : ℝ)^1024 ≤ (1250153291229917/1250000000000000 : ℝ)^4411 := by
      have hnat : (10005283387645179501 : ℕ)^1024*1250000000000000^4411 ≤ 1250153291229917^4411*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005283387645179501 10000000000000000000 1250153291229917 1250000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250153291229917/1250000000000000 : ℝ)) (X := (10005283387645179501/10000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4307033784795253/50000000000000000000 : ℝ) ≤ ((16910971708848328591/16915000000000000000 : ℝ)+2*(413205232237/338300000000000 : ℝ)*(5693/50000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (16910971708848328591/16915000000000000000 : ℝ)+2*(413205232237/338300000000000 : ℝ)*(5693/50000 : ℝ)=(5000199959687431/5000000000000000 : ℝ) by norm_num, show 1+2*(4307033784795253/50000000000000000000 : ℝ)=(25004307033784795253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5283387645179501/20000000000000000000 : ℝ)+(4307033784795253/50000000000000000000 : ℝ) ≤ ((16910971708848328591/16915000000000000000 : ℝ)+(413205232237/338300000000000 : ℝ)*((14769/100000 : ℝ)+(5693/50000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (16910971708848328591/16915000000000000000 : ℝ)+(413205232237/338300000000000 : ℝ)*((14769/100000 : ℝ)+(5693/50000 : ℝ))=(10000813124607099/10000000000000000 : ℝ) by norm_num, show 1+(5283387645179501/20000000000000000000 : ℝ)+(4307033784795253/50000000000000000000 : ℝ)=(100035031005795488011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5283387645179501/20000000000000000000 : ℝ) ≤ ((16910971708848328591/16915000000000000000 : ℝ)+2*(413205232237/338300000000000 : ℝ)*(14769/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (16910971708848328591/16915000000000000000 : ℝ)+2*(413205232237/338300000000000 : ℝ)*(14769/100000 : ℝ)=(1250153291229917/1250000000000000 : ℝ) by norm_num, show 1+2*(5283387645179501/20000000000000000000 : ℝ)=(10005283387645179501/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16910971708848328591/16915000000000000000 : ℝ)*(X 1 0+X 2 0)+(413205232237/338300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (16910971708848328591/16915000000000000000 : ℝ)) (alpha := (413205232237/338300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16910971708848328591/16915000000000000000 : ℝ)*(X 0 1+X 2 1)+(413205232237/338300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (16910971708848328591/16915000000000000000 : ℝ)) (alpha := (413205232237/338300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16910971708848328591/16915000000000000000 : ℝ)*(X 0 2+X 1 2)+(413205232237/338300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (5693/50000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (16910971708848328591/16915000000000000000 : ℝ)) (alpha := (413205232237/338300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1952623181/10000000000 : ℝ)*X 0 0+(5407018909/10000000000 : ℝ)*X 0 1+(5247410311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346828321/10000000000 : ℝ)*X 1 0+(-2033865783/10000000000 : ℝ)*X 1 1+(262370581/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346825167/10000000000 : ℝ)*X 2 0+(2623708811/5000000000 : ℝ)*X 2 1+(-1016931007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298657249/10000000000 : ℝ)*X 0 0+(2063850611/5000000000 : ℝ)*X 0 1+(895178119/2000000000 : ℝ)*X 0 2+(4298657249/10000000000 : ℝ)*X 1 0+(2063850611/5000000000 : ℝ)*X 1 1+(895178119/2000000000 : ℝ)*X 1 2+(4298657249/10000000000 : ℝ)*X 2 0+(2063850611/5000000000 : ℝ)*X 2 1+(895178119/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1952632723/10000000000 : ℝ)*X 0 0+(5247989503/10000000000 : ℝ)*X 0 1+(1081287581/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132631113/250000000 : ℝ)*X 1 0+(-1874838093/10000000000 : ℝ)*X 1 1+(5406437909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305244501/10000000000 : ℝ)*X 2 0+(2703218957/5000000000 : ℝ)*X 2 1+(-937419057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074670197/2500000000 : ℝ)*X 0 0+(4474633277/10000000000 : ℝ)*X 0 1+(4128965753/10000000000 : ℝ)*X 0 2+(1074670197/2500000000 : ℝ)*X 1 0+(4474633277/10000000000 : ℝ)*X 1 1+(4128965753/10000000000 : ℝ)*X 1 2+(1074670197/2500000000 : ℝ)*X 2 0+(4474633277/10000000000 : ℝ)*X 2 1+(4128965753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1049021977/1250000000 : ℝ)*X 2 0+(1248493577/5000000000 : ℝ)*X 2 1+(-842996723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_s7_8 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (689917546724101441042464489/422875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (260943621/50000000000000 : ℝ)*(upper2) + (239988967/100000000000000 : ℝ)*(upper4) + (162717147/12500000000000 : ℝ)*(upper5) + (4568867062203707/100000000000000 : ℝ)*(major0) + (4568867062203707/100000000000000 : ℝ)*(major1) + (1142216765550927/25000000000000 : ℝ)*(major2) + (1566367013475081/25000000000000 : ℝ)*(sp0) + (6265519627124417/100000000000000 : ℝ)*(sp1) + (1253130845084907/20000000000000 : ℝ)*(sp2) + (143602411482653/5000000000000 : ℝ)*(sp3) + (189846948339/100000000000000 : ℝ)*(sp4) + (138273724247/100000000000000 : ℝ)*(sp5) + (3492440323/12500000000000 : ℝ)*(sp7) + (28714251/781250000000 : ℝ)*(sp8) + (718019042293911/25000000000000 : ℝ)*(f.failure) + (783207237606083/12500000000000 : ℝ)*(f.sum) + (18794675096393/1353200000000000000000000000 : ℝ)*base65 + (403633279682586837/1691500000000000000000000000000000 : ℝ)*base67 + (3277129402746016357/422875000000000000000000000000000 : ℝ)*base69 + (34945992760200586837/1691500000000000000000000000000000 : ℝ)*base71 + (1524866173411/270640000000000000000000000 : ℝ)*base73 + (137406290632983643/422875000000000000000000000000000 : ℝ)*base76 + (15392447854604736837/1691500000000000000000000000000000 : ℝ)*base77 + (7515528766087236837/1691500000000000000000000000000000 : ℝ)*base79 + (10695272382089/16915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (349859/156250000000000000000 : ℝ)*base90 + (349859/156250000000000000000 : ℝ)*base92 + (1912359/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1198658773939094692116878073/211437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192102329/20000000000000 : ℝ)*(base19) + (206424199/20000000000000 : ℝ)*(base23) + (164775091/50000000000000 : ℝ)*(lower1) + (14273911/12500000000000 : ℝ)*(upper3) + (1859097/4000000000000 : ℝ)*(lower4) + (59516113/50000000000000 : ℝ)*(upper5) + (2301031077019899/50000000000000 : ℝ)*(major0) + (2301031077019899/50000000000000 : ℝ)*(major1) + (2301031077019899/50000000000000 : ℝ)*(major2) + (842775837/100000000000000 : ℝ)*(sp2) + (788897610993433/12500000000000 : ℝ)*(sp4) + (6311179927435819/100000000000000 : ℝ)*(sp5) + (6311179013050633/100000000000000 : ℝ)*(sp6) + (180808951947647/6250000000000 : ℝ)*(sp7) + (180808951947647/6250000000000 : ℝ)*(f.failure) + (788897610993433/12500000000000 : ℝ)*(f.sum) + (44200129171517/8457500000000000000000000000 : ℝ)*base66 + (5025670544058782309/845750000000000000000000000000000 : ℝ)*base67 + (3633823084398782309/845750000000000000000000000000000 : ℝ)*base69 + (69729239398161217691/845750000000000000000000000000000 : ℝ)*base72 + (22648316257771/16915000000000000000000000000 : ℝ)*base73 + (84836107784140532309/845750000000000000000000000000000 : ℝ)*base75 + (8953042274524782309/845750000000000000000000000000000 : ℝ)*base77 + (3981144949990782309/845750000000000000000000000000000 : ℝ)*base79 + (56880630371957/8457500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (183893/39062500000000000000 : ℝ)*base90 + (183893/39062500000000000000 : ℝ)*base92 + (183893/39062500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1452_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5693/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1452_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1452_box_0 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-22420073/125000000 : ℝ)*x 0 + (2692633903/5000000000 : ℝ)*x 1 + (673158491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22420073/125000000 : ℝ)^1103 ≤ (2134032650233/20000000000000 : ℝ)^847 := by
    have hnat : (22420073 : ℕ)^1103*20000000000000^847 ≤ 2134032650233^847*125000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22420073 125000000 2134032650233 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692633903/5000000000 : ℝ)^1103 ≤ (2791557356659/6250000000000 : ℝ)^847 := by
    have hnat : (2692633903 : ℕ)^1103*6250000000000^847 ≤ 2791557356659^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692633903 5000000000 2791557356659 6250000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673158491/1250000000 : ℝ)^1103 ≤ (11166229756057/25000000000000 : ℝ)^847 := by
    have hnat : (673158491 : ℕ)^1103*25000000000000^847 ≤ 11166229756057^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673158491 1250000000 11166229756057 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22420073/125000000 : ℝ), (2692633903/5000000000 : ℝ), (673158491/1250000000 : ℝ)] ![(2134032650233/20000000000000 : ℝ), (2791557356659/6250000000000 : ℝ), (11166229756057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22420073/125000000 : ℝ)|^1103 ≤ (2134032650233/20000000000000 : ℝ)^847
        have hw : |(-22420073/125000000 : ℝ)|=(22420073/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692633903/5000000000 : ℝ)|^1103 ≤ (2791557356659/6250000000000 : ℝ)^847
        have hw : |(2692633903/5000000000 : ℝ)|=(2692633903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673158491/1250000000 : ℝ)|^1103 ≤ (11166229756057/25000000000000 : ℝ)^847
        have hw : |(673158491/1250000000 : ℝ)|=(673158491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_1 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2643105049/5000000000 : ℝ)*x 0 + (-192978691/1000000000 : ℝ)*x 1 + (5385268417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643105049/5000000000 : ℝ)^1103 ≤ (8719602677247/20000000000000 : ℝ)^847 := by
    have hnat : (2643105049 : ℕ)^1103*20000000000000^847 ≤ 8719602677247^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643105049 5000000000 8719602677247 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192978691/1000000000 : ℝ)^1103 ≤ (11737062292891/100000000000000 : ℝ)^847 := by
    have hnat : (192978691 : ℕ)^1103*100000000000000^847 ≤ 11737062292891^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192978691 1000000000 11737062292891 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385268417/10000000000 : ℝ)^1103 ≤ (44664924305763/100000000000000 : ℝ)^847 := by
    have hnat : (5385268417 : ℕ)^1103*100000000000000^847 ≤ 44664924305763^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385268417 10000000000 44664924305763 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643105049/5000000000 : ℝ), (-192978691/1000000000 : ℝ), (5385268417/10000000000 : ℝ)] ![(8719602677247/20000000000000 : ℝ), (11737062292891/100000000000000 : ℝ), (44664924305763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643105049/5000000000 : ℝ)|^1103 ≤ (8719602677247/20000000000000 : ℝ)^847
        have hw : |(2643105049/5000000000 : ℝ)|=(2643105049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192978691/1000000000 : ℝ)|^1103 ≤ (11737062292891/100000000000000 : ℝ)^847
        have hw : |(-192978691/1000000000 : ℝ)|=(192978691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385268417/10000000000 : ℝ)|^1103 ≤ (44664924305763/100000000000000 : ℝ)^847
        have hw : |(5385268417/10000000000 : ℝ)|=(5385268417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_2 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5286211009/10000000000 : ℝ)*x 0 + (1346317/2500000 : ℝ)*x 1 + (-1929786243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286211009/10000000000 : ℝ)^1103 ≤ (43598023170603/100000000000000 : ℝ)^847 := by
    have hnat : (5286211009 : ℕ)^1103*100000000000000^847 ≤ 43598023170603^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286211009 10000000000 43598023170603 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346317/2500000 : ℝ)^1103 ≤ (44664919801877/100000000000000 : ℝ)^847 := by
    have hnat : (1346317 : ℕ)^1103*100000000000000^847 ≤ 44664919801877^847*2500000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346317 2500000 44664919801877 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929786243/10000000000 : ℝ)^1103 ≤ (2347411402009/20000000000000 : ℝ)^847 := by
    have hnat : (1929786243 : ℕ)^1103*20000000000000^847 ≤ 2347411402009^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929786243 10000000000 2347411402009 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286211009/10000000000 : ℝ), (1346317/2500000 : ℝ), (-1929786243/10000000000 : ℝ)] ![(43598023170603/100000000000000 : ℝ), (44664919801877/100000000000000 : ℝ), (2347411402009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286211009/10000000000 : ℝ)|^1103 ≤ (43598023170603/100000000000000 : ℝ)^847
        have hw : |(5286211009/10000000000 : ℝ)|=(5286211009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346317/2500000 : ℝ)|^1103 ≤ (44664919801877/100000000000000 : ℝ)^847
        have hw : |(1346317/2500000 : ℝ)|=(1346317/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1929786243/10000000000 : ℝ)|^1103 ≤ (2347411402009/20000000000000 : ℝ)^847
        have hw : |(-1929786243/10000000000 : ℝ)|=(1929786243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_3 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2222250843/5000000000 : ℝ)*x 0 + (1057349647/2500000000 : ℝ)*x 1 + (4229399303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2222250843/5000000000 : ℝ)^1103 ≤ (695680749981/2000000000000 : ℝ)^847 := by
    have hnat : (2222250843 : ℕ)^1103*2000000000000^847 ≤ 695680749981^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222250843 5000000000 695680749981 2000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057349647/2500000000 : ℝ)^1103 ≤ (12737491271/39062500000 : ℝ)^847 := by
    have hnat : (1057349647 : ℕ)^1103*39062500000^847 ≤ 12737491271^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057349647 2500000000 12737491271 39062500000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229399303/10000000000 : ℝ)^1103 ≤ (1630399241621/5000000000000 : ℝ)^847 := by
    have hnat : (4229399303 : ℕ)^1103*5000000000000^847 ≤ 1630399241621^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229399303 10000000000 1630399241621 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2222250843/5000000000 : ℝ), (1057349647/2500000000 : ℝ), (4229399303/10000000000 : ℝ)] ![(695680749981/2000000000000 : ℝ), (12737491271/39062500000 : ℝ), (1630399241621/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2222250843/5000000000 : ℝ)|^1103 ≤ (695680749981/2000000000000 : ℝ)^847
        have hw : |(2222250843/5000000000 : ℝ)|=(2222250843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057349647/2500000000 : ℝ)|^1103 ≤ (12737491271/39062500000 : ℝ)^847
        have hw : |(1057349647/2500000000 : ℝ)|=(1057349647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229399303/10000000000 : ℝ)|^1103 ≤ (1630399241621/5000000000000 : ℝ)^847
        have hw : |(4229399303/10000000000 : ℝ)|=(4229399303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_4 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1057184377/5000000000 : ℝ)*x 0 + (5266846187/10000000000 : ℝ)*x 1 + (1316711587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057184377/5000000000 : ℝ)^1103 ≤ (13219687519333/100000000000000 : ℝ)^847 := by
    have hnat : (1057184377 : ℕ)^1103*100000000000000^847 ≤ 13219687519333^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057184377 5000000000 13219687519333 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266846187/10000000000 : ℝ)^1103 ≤ (21695077685821/50000000000000 : ℝ)^847 := by
    have hnat : (5266846187 : ℕ)^1103*50000000000000^847 ≤ 21695077685821^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266846187 10000000000 21695077685821 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316711587/2500000000 : ℝ)^1103 ≤ (8678031419781/20000000000000 : ℝ)^847 := by
    have hnat : (1316711587 : ℕ)^1103*20000000000000^847 ≤ 8678031419781^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316711587 2500000000 8678031419781 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1057184377/5000000000 : ℝ), (5266846187/10000000000 : ℝ), (1316711587/2500000000 : ℝ)] ![(13219687519333/100000000000000 : ℝ), (21695077685821/50000000000000 : ℝ), (8678031419781/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1057184377/5000000000 : ℝ)|^1103 ≤ (13219687519333/100000000000000 : ℝ)^847
        have hw : |(-1057184377/5000000000 : ℝ)|=(1057184377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266846187/10000000000 : ℝ)|^1103 ≤ (21695077685821/50000000000000 : ℝ)^847
        have hw : |(5266846187/10000000000 : ℝ)|=(5266846187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316711587/2500000000 : ℝ)|^1103 ≤ (8678031419781/20000000000000 : ℝ)^847
        have hw : |(1316711587/2500000000 : ℝ)|=(1316711587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_5 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369011027/10000000000 : ℝ)*x 0 + (-395601801/2000000000 : ℝ)*x 1 + (5266846271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369011027/10000000000 : ℝ)^1103 ≤ (5561176687627/12500000000000 : ℝ)^847 := by
    have hnat : (5369011027 : ℕ)^1103*12500000000000^847 ≤ 5561176687627^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369011027 10000000000 5561176687627 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395601801/2000000000 : ℝ)^1103 ≤ (12120430204089/100000000000000 : ℝ)^847 := by
    have hnat : (395601801 : ℕ)^1103*100000000000000^847 ≤ 12120430204089^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395601801 2000000000 12120430204089 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266846271/10000000000 : ℝ)^1103 ≤ (43390156272823/100000000000000 : ℝ)^847 := by
    have hnat : (5266846271 : ℕ)^1103*100000000000000^847 ≤ 43390156272823^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266846271 10000000000 43390156272823 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369011027/10000000000 : ℝ), (-395601801/2000000000 : ℝ), (5266846271/10000000000 : ℝ)] ![(5561176687627/12500000000000 : ℝ), (12120430204089/100000000000000 : ℝ), (43390156272823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369011027/10000000000 : ℝ)|^1103 ≤ (5561176687627/12500000000000 : ℝ)^847
        have hw : |(5369011027/10000000000 : ℝ)|=(5369011027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-395601801/2000000000 : ℝ)|^1103 ≤ (12120430204089/100000000000000 : ℝ)^847
        have hw : |(-395601801/2000000000 : ℝ)|=(395601801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266846271/10000000000 : ℝ)|^1103 ≤ (43390156272823/100000000000000 : ℝ)^847
        have hw : |(5266846271/10000000000 : ℝ)|=(5266846271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_6 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369011049/10000000000 : ℝ)*x 0 + (2633423097/5000000000 : ℝ)*x 1 + (-49450227/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369011049/10000000000 : ℝ)^1103 ≤ (22244706869207/50000000000000 : ℝ)^847 := by
    have hnat : (5369011049 : ℕ)^1103*50000000000000^847 ≤ 22244706869207^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369011049 10000000000 22244706869207 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633423097/5000000000 : ℝ)^1103 ≤ (2169507772337/5000000000000 : ℝ)^847 := by
    have hnat : (2633423097 : ℕ)^1103*5000000000000^847 ≤ 2169507772337^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633423097 5000000000 2169507772337 5000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49450227/250000000 : ℝ)^1103 ≤ (18938173129/156250000000 : ℝ)^847 := by
    have hnat : (49450227 : ℕ)^1103*156250000000^847 ≤ 18938173129^847*250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49450227 250000000 18938173129 156250000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369011049/10000000000 : ℝ), (2633423097/5000000000 : ℝ), (-49450227/250000000 : ℝ)] ![(22244706869207/50000000000000 : ℝ), (2169507772337/5000000000000 : ℝ), (18938173129/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369011049/10000000000 : ℝ)|^1103 ≤ (22244706869207/50000000000000 : ℝ)^847
        have hw : |(5369011049/10000000000 : ℝ)|=(5369011049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633423097/5000000000 : ℝ)|^1103 ≤ (2169507772337/5000000000000 : ℝ)^847
        have hw : |(2633423097/5000000000 : ℝ)|=(2633423097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49450227/250000000 : ℝ)|^1103 ≤ (18938173129/156250000000 : ℝ)^847
        have hw : |(-49450227/250000000 : ℝ)|=(49450227/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_7 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1037933149/2500000000 : ℝ)*x 0 + (4375733271/10000000000 : ℝ)*x 1 + (4375733219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037933149/2500000000 : ℝ)^1103 ≤ (1273215113057/4000000000000 : ℝ)^847 := by
    have hnat : (1037933149 : ℕ)^1103*4000000000000^847 ≤ 1273215113057^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037933149 2500000000 1273215113057 4000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4375733271/10000000000 : ℝ)^1103 ≤ (6816962269459/20000000000000 : ℝ)^847 := by
    have hnat : (4375733271 : ℕ)^1103*20000000000000^847 ≤ 6816962269459^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375733271 10000000000 6816962269459 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4375733219/10000000000 : ℝ)^1103 ≤ (4260601352477/12500000000000 : ℝ)^847 := by
    have hnat : (4375733219 : ℕ)^1103*12500000000000^847 ≤ 4260601352477^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375733219 10000000000 4260601352477 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037933149/2500000000 : ℝ), (4375733271/10000000000 : ℝ), (4375733219/10000000000 : ℝ)] ![(1273215113057/4000000000000 : ℝ), (6816962269459/20000000000000 : ℝ), (4260601352477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037933149/2500000000 : ℝ)|^1103 ≤ (1273215113057/4000000000000 : ℝ)^847
        have hw : |(1037933149/2500000000 : ℝ)|=(1037933149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4375733271/10000000000 : ℝ)|^1103 ≤ (6816962269459/20000000000000 : ℝ)^847
        have hw : |(4375733271/10000000000 : ℝ)|=(4375733271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4375733219/10000000000 : ℝ)|^1103 ≤ (4260601352477/12500000000000 : ℝ)^847
        have hw : |(4375733219/10000000000 : ℝ)|=(4375733219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_8 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046757931/10000000000 : ℝ)*x 0 + (5184833561/10000000000 : ℝ)*x 1 + (1349806797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046757931/10000000000 : ℝ)^1103 ≤ (12671878582709/100000000000000 : ℝ)^847 := by
    have hnat : (2046757931 : ℕ)^1103*100000000000000^847 ≤ 12671878582709^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046757931 10000000000 12671878582709 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184833561/10000000000 : ℝ)^1103 ≤ (42512373769041/100000000000000 : ℝ)^847 := by
    have hnat : (5184833561 : ℕ)^1103*100000000000000^847 ≤ 42512373769041^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184833561 10000000000 42512373769041 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349806797/2500000000 : ℝ)^1103 ≤ (22407873816057/50000000000000 : ℝ)^847 := by
    have hnat : (1349806797 : ℕ)^1103*50000000000000^847 ≤ 22407873816057^847*2500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349806797 2500000000 22407873816057 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046757931/10000000000 : ℝ), (5184833561/10000000000 : ℝ), (1349806797/2500000000 : ℝ)] ![(12671878582709/100000000000000 : ℝ), (42512373769041/100000000000000 : ℝ), (22407873816057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046757931/10000000000 : ℝ)|^1103 ≤ (12671878582709/100000000000000 : ℝ)^847
        have hw : |(-2046757931/10000000000 : ℝ)|=(2046757931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184833561/10000000000 : ℝ)|^1103 ≤ (42512373769041/100000000000000 : ℝ)^847
        have hw : |(5184833561/10000000000 : ℝ)|=(5184833561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349806797/2500000000 : ℝ)|^1103 ≤ (22407873816057/50000000000000 : ℝ)^847
        have hw : |(1349806797/2500000000 : ℝ)|=(1349806797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_9 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276446749/10000000000 : ℝ)*x 0 + (-961988737/5000000000 : ℝ)*x 1 + (168725849/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276446749/10000000000 : ℝ)^1103 ≤ (1739727274389/4000000000000 : ℝ)^847 := by
    have hnat : (5276446749 : ℕ)^1103*4000000000000^847 ≤ 1739727274389^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276446749 10000000000 1739727274389 4000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (961988737/5000000000 : ℝ)^1103 ≤ (11691070708937/100000000000000 : ℝ)^847 := by
    have hnat : (961988737 : ℕ)^1103*100000000000000^847 ≤ 11691070708937^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961988737 5000000000 11691070708937 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168725849/312500000 : ℝ)^1103 ≤ (44815747415931/100000000000000 : ℝ)^847 := by
    have hnat : (168725849 : ℕ)^1103*100000000000000^847 ≤ 44815747415931^847*312500000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168725849 312500000 44815747415931 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276446749/10000000000 : ℝ), (-961988737/5000000000 : ℝ), (168725849/312500000 : ℝ)] ![(1739727274389/4000000000000 : ℝ), (11691070708937/100000000000000 : ℝ), (44815747415931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276446749/10000000000 : ℝ)|^1103 ≤ (1739727274389/4000000000000 : ℝ)^847
        have hw : |(5276446749/10000000000 : ℝ)|=(5276446749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-961988737/5000000000 : ℝ)|^1103 ≤ (11691070708937/100000000000000 : ℝ)^847
        have hw : |(-961988737/5000000000 : ℝ)|=(961988737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168725849/312500000 : ℝ)|^1103 ≤ (44815747415931/100000000000000 : ℝ)^847
        have hw : |(168725849/312500000 : ℝ)|=(168725849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_10 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2638223423/5000000000 : ℝ)*x 0 + (5399227093/10000000000 : ℝ)*x 1 + (-384795489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638223423/5000000000 : ℝ)^1103 ≤ (10873295725237/25000000000000 : ℝ)^847 := by
    have hnat : (2638223423 : ℕ)^1103*25000000000000^847 ≤ 10873295725237^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638223423 5000000000 10873295725237 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399227093/10000000000 : ℝ)^1103 ≤ (22407873302623/50000000000000 : ℝ)^847 := by
    have hnat : (5399227093 : ℕ)^1103*50000000000000^847 ≤ 22407873302623^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399227093 10000000000 22407873302623 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (384795489/2000000000 : ℝ)^1103 ≤ (11691070479457/100000000000000 : ℝ)^847 := by
    have hnat : (384795489 : ℕ)^1103*100000000000000^847 ≤ 11691070479457^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384795489 2000000000 11691070479457 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638223423/5000000000 : ℝ), (5399227093/10000000000 : ℝ), (-384795489/2000000000 : ℝ)] ![(10873295725237/25000000000000 : ℝ), (22407873302623/50000000000000 : ℝ), (11691070479457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638223423/5000000000 : ℝ)|^1103 ≤ (10873295725237/25000000000000 : ℝ)^847
        have hw : |(2638223423/5000000000 : ℝ)|=(2638223423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399227093/10000000000 : ℝ)|^1103 ≤ (22407873302623/50000000000000 : ℝ)^847
        have hw : |(5399227093/10000000000 : ℝ)|=(5399227093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-384795489/2000000000 : ℝ)|^1103 ≤ (11691070479457/100000000000000 : ℝ)^847
        have hw : |(-384795489/2000000000 : ℝ)|=(384795489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_11 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4478456271/10000000000 : ℝ)*x 0 + (4212134627/10000000000 : ℝ)*x 1 + (4212134697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478456271/10000000000 : ℝ)^1103 ≤ (7026098633313/20000000000000 : ℝ)^847 := by
    have hnat : (4478456271 : ℕ)^1103*20000000000000^847 ≤ 7026098633313^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478456271 10000000000 7026098633313 20000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4212134627/10000000000 : ℝ)^1103 ≤ (32434753056811/100000000000000 : ℝ)^847 := by
    have hnat : (4212134627 : ℕ)^1103*100000000000000^847 ≤ 32434753056811^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212134627 10000000000 32434753056811 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212134697/10000000000 : ℝ)^1103 ≤ (32434753758749/100000000000000 : ℝ)^847 := by
    have hnat : (4212134697 : ℕ)^1103*100000000000000^847 ≤ 32434753758749^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212134697 10000000000 32434753758749 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478456271/10000000000 : ℝ), (4212134627/10000000000 : ℝ), (4212134697/10000000000 : ℝ)] ![(7026098633313/20000000000000 : ℝ), (32434753056811/100000000000000 : ℝ), (32434753758749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478456271/10000000000 : ℝ)|^1103 ≤ (7026098633313/20000000000000 : ℝ)^847
        have hw : |(4478456271/10000000000 : ℝ)|=(4478456271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4212134627/10000000000 : ℝ)|^1103 ≤ (32434753056811/100000000000000 : ℝ)^847
        have hw : |(4212134627/10000000000 : ℝ)|=(4212134627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212134697/10000000000 : ℝ)|^1103 ≤ (32434753758749/100000000000000 : ℝ)^847
        have hw : |(4212134697/10000000000 : ℝ)|=(4212134697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_12 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1861359129/10000000000 : ℝ)*x 0 + (2732650343/5000000000 : ℝ)*x 1 + (5255709559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1861359129/10000000000 : ℝ)^1103 ≤ (5599010794711/50000000000000 : ℝ)^847 := by
    have hnat : (1861359129 : ℕ)^1103*50000000000000^847 ≤ 5599010794711^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1861359129 10000000000 5599010794711 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732650343/5000000000 : ℝ)^1103 ≤ (45531262400059/100000000000000 : ℝ)^847 := by
    have hnat : (2732650343 : ℕ)^1103*100000000000000^847 ≤ 45531262400059^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732650343 5000000000 45531262400059 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255709559/10000000000 : ℝ)^1103 ≤ (43270715997613/100000000000000 : ℝ)^847 := by
    have hnat : (5255709559 : ℕ)^1103*100000000000000^847 ≤ 43270715997613^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255709559 10000000000 43270715997613 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1861359129/10000000000 : ℝ), (2732650343/5000000000 : ℝ), (5255709559/10000000000 : ℝ)] ![(5599010794711/50000000000000 : ℝ), (45531262400059/100000000000000 : ℝ), (43270715997613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1861359129/10000000000 : ℝ)|^1103 ≤ (5599010794711/50000000000000 : ℝ)^847
        have hw : |(-1861359129/10000000000 : ℝ)|=(1861359129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732650343/5000000000 : ℝ)|^1103 ≤ (45531262400059/100000000000000 : ℝ)^847
        have hw : |(2732650343/5000000000 : ℝ)|=(2732650343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255709559/10000000000 : ℝ)|^1103 ≤ (43270715997613/100000000000000 : ℝ)^847
        have hw : |(5255709559/10000000000 : ℝ)|=(5255709559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_13 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1075359237/2000000000 : ℝ)*x 0 + (-1982445237/10000000000 : ℝ)*x 1 + (2627854883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075359237/2000000000 : ℝ)^1103 ≤ (44573440149547/100000000000000 : ℝ)^847 := by
    have hnat : (1075359237 : ℕ)^1103*100000000000000^847 ≤ 44573440149547^847*2000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075359237 2000000000 44573440149547 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1982445237/10000000000 : ℝ)^1103 ≤ (3038960403479/25000000000000 : ℝ)^847 := by
    have hnat : (1982445237 : ℕ)^1103*25000000000000^847 ≤ 3038960403479^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982445237 10000000000 3038960403479 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627854883/5000000000 : ℝ)^1103 ≤ (33805248607/78125000000 : ℝ)^847 := by
    have hnat : (2627854883 : ℕ)^1103*78125000000^847 ≤ 33805248607^847*5000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627854883 5000000000 33805248607 78125000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075359237/2000000000 : ℝ), (-1982445237/10000000000 : ℝ), (2627854883/5000000000 : ℝ)] ![(44573440149547/100000000000000 : ℝ), (3038960403479/25000000000000 : ℝ), (33805248607/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075359237/2000000000 : ℝ)|^1103 ≤ (44573440149547/100000000000000 : ℝ)^847
        have hw : |(1075359237/2000000000 : ℝ)|=(1075359237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1982445237/10000000000 : ℝ)|^1103 ≤ (3038960403479/25000000000000 : ℝ)^847
        have hw : |(-1982445237/10000000000 : ℝ)|=(1982445237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627854883/5000000000 : ℝ)|^1103 ≤ (33805248607/78125000000 : ℝ)^847
        have hw : |(2627854883/5000000000 : ℝ)|=(2627854883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_14 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (672099503/1250000000 : ℝ)*x 0 + (210228393/400000000 : ℝ)*x 1 + (-30975709/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672099503/1250000000 : ℝ)^1103 ≤ (5571679801433/12500000000000 : ℝ)^847 := by
    have hnat : (672099503 : ℕ)^1103*12500000000000^847 ≤ 5571679801433^847*1250000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672099503 1250000000 5571679801433 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210228393/400000000 : ℝ)^1103 ≤ (5408839856191/12500000000000 : ℝ)^847 := by
    have hnat : (210228393 : ℕ)^1103*12500000000000^847 ≤ 5408839856191^847*400000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210228393 400000000 5408839856191 12500000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30975709/156250000 : ℝ)^1103 ≤ (12155842723833/100000000000000 : ℝ)^847 := by
    have hnat : (30975709 : ℕ)^1103*100000000000000^847 ≤ 12155842723833^847*156250000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30975709 156250000 12155842723833 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672099503/1250000000 : ℝ), (210228393/400000000 : ℝ), (-30975709/156250000 : ℝ)] ![(5571679801433/12500000000000 : ℝ), (5408839856191/12500000000000 : ℝ), (12155842723833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672099503/1250000000 : ℝ)|^1103 ≤ (5571679801433/12500000000000 : ℝ)^847
        have hw : |(672099503/1250000000 : ℝ)|=(672099503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210228393/400000000 : ℝ)|^1103 ≤ (5408839856191/12500000000000 : ℝ)^847
        have hw : |(210228393/400000000 : ℝ)|=(210228393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30975709/156250000 : ℝ)|^1103 ≤ (12155842723833/100000000000000 : ℝ)^847
        have hw : |(-30975709/156250000 : ℝ)|=(30975709/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1452_box_15 (p : ℝ) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4123750193/10000000000 : ℝ)*x 0 + (438948361/1000000000 : ℝ)*x 1 + (219474161/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123750193/10000000000 : ℝ)^1103 ≤ (15775643276593/50000000000000 : ℝ)^847 := by
    have hnat : (4123750193 : ℕ)^1103*50000000000000^847 ≤ 15775643276593^847*10000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123750193 10000000000 15775643276593 50000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438948361/1000000000 : ℝ)^1103 ≤ (8556089674979/25000000000000 : ℝ)^847 := by
    have hnat : (438948361 : ℕ)^1103*25000000000000^847 ≤ 8556089674979^847*1000000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438948361 1000000000 8556089674979 25000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219474161/500000000 : ℝ)^1103 ≤ (34224354740067/100000000000000 : ℝ)^847 := by
    have hnat : (219474161 : ℕ)^1103*100000000000000^847 ≤ 34224354740067^847*500000000^1103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219474161 500000000 34224354740067 100000000000000 1103 847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1103/256 : ℝ)) 1103 847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123750193/10000000000 : ℝ), (438948361/1000000000 : ℝ), (219474161/500000000 : ℝ)] ![(15775643276593/50000000000000 : ℝ), (8556089674979/25000000000000 : ℝ), (34224354740067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123750193/10000000000 : ℝ)|^1103 ≤ (15775643276593/50000000000000 : ℝ)^847
        have hw : |(4123750193/10000000000 : ℝ)|=(4123750193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438948361/1000000000 : ℝ)|^1103 ≤ (8556089674979/25000000000000 : ℝ)^847
        have hw : |(438948361/1000000000 : ℝ)|=(438948361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219474161/500000000 : ℝ)|^1103 ≤ (34224354740067/100000000000000 : ℝ)^847
        have hw : |(219474161/500000000 : ℝ)|=(219474161/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1452_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31457/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1479/2500 : ℝ) ∧ (40287/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84771/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11387/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11387/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11387/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11387/100000 : ℝ) ^ (4411/1024 : ℝ) ≤ (4308663483351253/50000000000000000000 : ℝ) := by
    have hpowers : (11387/100000 : ℝ)^4411 ≤ (4308663483351253/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11387 : ℕ)^4411*50000000000000000000^1024 ≤ 4308663483351253^1024*100000^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11387 100000 4308663483351253 50000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11387/100000 : ℝ)) (X := (4308663483351253/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (4411/1024 : ℝ) ≤ (13204617081147911/50000000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^4411 ≤ (13204617081147911/50000000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4411*50000000000000000000^1024 ≤ 13204617081147911^1024*6250^4411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 13204617081147911 50000000000000000000 4411 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (13204617081147911/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004308663483351253/25000000000000000000 : ℝ) ≤ (10000400070686633/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (25004308663483351253/25000000000000000000 : ℝ)^1024 ≤ (10000400070686633/10000000000000000 : ℝ)^4411 := by
      have hnat : (25004308663483351253 : ℕ)^1024*10000000000000000^4411 ≤ 10000400070686633^4411*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004308663483351253 25000000000000000000 10000400070686633 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000400070686633/10000000000000000 : ℝ)) (X := (25004308663483351253/25000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504378320141124791/12500000000000000000 : ℝ) ≤ (5000406510726643/5000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (12504378320141124791/12500000000000000000 : ℝ)^1024 ≤ (5000406510726643/5000000000000000 : ℝ)^4411 := by
      have hnat : (12504378320141124791 : ℕ)^1024*5000000000000000^4411 ≤ 5000406510726643^4411*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504378320141124791 12500000000000000000 5000406510726643 5000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000406510726643/5000000000000000 : ℝ)) (X := (12504378320141124791/12500000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013204617081147911/25000000000000000000 : ℝ) ≤ (10001225972219939/10000000000000000 : ℝ) ^ (4411/1024 : ℝ) := by
    have hpowers : (25013204617081147911/25000000000000000000 : ℝ)^1024 ≤ (10001225972219939/10000000000000000 : ℝ)^4411 := by
      have hnat : (25013204617081147911 : ℕ)^1024*10000000000000000^4411 ≤ 10001225972219939^4411*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013204617081147911 25000000000000000000 10001225972219939 10000000000000000 1024 4411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001225972219939/10000000000000000 : ℝ)) (X := (25013204617081147911/25000000000000000000 : ℝ)) (by norm_num) 4411 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4308663483351253/50000000000000000000 : ℝ) ≤ ((11267316032743916917/11270000000000000000 : ℝ)+2*(137650255551/112700000000000 : ℝ)*(11387/100000 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (11267316032743916917/11270000000000000000 : ℝ)+2*(137650255551/112700000000000 : ℝ)*(11387/100000 : ℝ)=(10000400070686633/10000000000000000 : ℝ) by norm_num, show 1+2*(4308663483351253/50000000000000000000 : ℝ)=(25004308663483351253/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13204617081147911/50000000000000000000 : ℝ)+(4308663483351253/50000000000000000000 : ℝ) ≤ ((11267316032743916917/11270000000000000000 : ℝ)+(137650255551/112700000000000 : ℝ)*((923/6250 : ℝ)+(11387/100000 : ℝ)))^(4411/1024 : ℝ) := by
    rw [show (11267316032743916917/11270000000000000000 : ℝ)+(137650255551/112700000000000 : ℝ)*((923/6250 : ℝ)+(11387/100000 : ℝ))=(5000406510726643/5000000000000000 : ℝ) by norm_num, show 1+(13204617081147911/50000000000000000000 : ℝ)+(4308663483351253/50000000000000000000 : ℝ)=(12504378320141124791/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13204617081147911/50000000000000000000 : ℝ) ≤ ((11267316032743916917/11270000000000000000 : ℝ)+2*(137650255551/112700000000000 : ℝ)*(923/6250 : ℝ))^(4411/1024 : ℝ) := by
    rw [show (11267316032743916917/11270000000000000000 : ℝ)+2*(137650255551/112700000000000 : ℝ)*(923/6250 : ℝ)=(10001225972219939/10000000000000000 : ℝ) by norm_num, show 1+2*(13204617081147911/50000000000000000000 : ℝ)=(25013204617081147911/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11267316032743916917/11270000000000000000 : ℝ)*(X 1 0+X 2 0)+(137650255551/112700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (11267316032743916917/11270000000000000000 : ℝ)) (alpha := (137650255551/112700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11267316032743916917/11270000000000000000 : ℝ)*(X 0 1+X 2 1)+(137650255551/112700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (11267316032743916917/11270000000000000000 : ℝ)) (alpha := (137650255551/112700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11267316032743916917/11270000000000000000 : ℝ)*(X 0 2+X 1 2)+(137650255551/112700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4411/1024 : ℝ)) (lo := (11387/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (11267316032743916917/11270000000000000000 : ℝ)) (alpha := (137650255551/112700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-22420073/125000000 : ℝ)*X 0 0+(2692633903/5000000000 : ℝ)*X 0 1+(673158491/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643105049/5000000000 : ℝ)*X 1 0+(-192978691/1000000000 : ℝ)*X 1 1+(5385268417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286211009/10000000000 : ℝ)*X 2 0+(1346317/2500000 : ℝ)*X 2 1+(-1929786243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2222250843/5000000000 : ℝ)*X 0 0+(1057349647/2500000000 : ℝ)*X 0 1+(4229399303/10000000000 : ℝ)*X 0 2+(2222250843/5000000000 : ℝ)*X 1 0+(1057349647/2500000000 : ℝ)*X 1 1+(4229399303/10000000000 : ℝ)*X 1 2+(2222250843/5000000000 : ℝ)*X 2 0+(1057349647/2500000000 : ℝ)*X 2 1+(4229399303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1057184377/5000000000 : ℝ)*X 0 0+(5266846187/10000000000 : ℝ)*X 0 1+(1316711587/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369011027/10000000000 : ℝ)*X 1 0+(-395601801/2000000000 : ℝ)*X 1 1+(5266846271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369011049/10000000000 : ℝ)*X 2 0+(2633423097/5000000000 : ℝ)*X 2 1+(-49450227/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037933149/2500000000 : ℝ)*X 0 0+(4375733271/10000000000 : ℝ)*X 0 1+(4375733219/10000000000 : ℝ)*X 0 2+(1037933149/2500000000 : ℝ)*X 1 0+(4375733271/10000000000 : ℝ)*X 1 1+(4375733219/10000000000 : ℝ)*X 1 2+(1037933149/2500000000 : ℝ)*X 2 0+(4375733271/10000000000 : ℝ)*X 2 1+(4375733219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2046757931/10000000000 : ℝ)*X 0 0+(5184833561/10000000000 : ℝ)*X 0 1+(1349806797/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276446749/10000000000 : ℝ)*X 1 0+(-961988737/5000000000 : ℝ)*X 1 1+(168725849/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638223423/5000000000 : ℝ)*X 2 0+(5399227093/10000000000 : ℝ)*X 2 1+(-384795489/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4478456271/10000000000 : ℝ)*X 0 0+(4212134627/10000000000 : ℝ)*X 0 1+(4212134697/10000000000 : ℝ)*X 0 2+(4478456271/10000000000 : ℝ)*X 1 0+(4212134627/10000000000 : ℝ)*X 1 1+(4212134697/10000000000 : ℝ)*X 1 2+(4478456271/10000000000 : ℝ)*X 2 0+(4212134627/10000000000 : ℝ)*X 2 1+(4212134697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1861359129/10000000000 : ℝ)*X 0 0+(2732650343/5000000000 : ℝ)*X 0 1+(5255709559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1075359237/2000000000 : ℝ)*X 1 0+(-1982445237/10000000000 : ℝ)*X 1 1+(2627854883/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((672099503/1250000000 : ℝ)*X 2 0+(210228393/400000000 : ℝ)*X 2 1+(-30975709/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4123750193/10000000000 : ℝ)*X 0 0+(438948361/1000000000 : ℝ)*X 0 1+(219474161/500000000 : ℝ)*X 0 2+(4123750193/10000000000 : ℝ)*X 1 0+(438948361/1000000000 : ℝ)*X 1 1+(219474161/500000000 : ℝ)*X 1 2+(4123750193/10000000000 : ℝ)*X 2 0+(438948361/1000000000 : ℝ)*X 2 1+(219474161/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1452_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31457/50000 : ℝ) ≤ (-88626864499390365368297319075921/140875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27670643/100000000000000 : ℝ)*(lower0) + (1891169/25000000000000 : ℝ)*(lower3) + (6828843/25000000000000 : ℝ)*(lower4) + (1520903034577329/50000000000000 : ℝ)*(major0) + (1520903034577329/50000000000000 : ℝ)*(major1) + (1520903034577329/50000000000000 : ℝ)*(major2) + (1852809373/100000000000000 : ℝ)*(sp1) + (6265719941/100000000000000 : ℝ)*(sp2) + (588174473/100000000000000 : ℝ)*(sp3) + (1048110860198981/25000000000000 : ℝ)*(sp4) + (4192444080439833/100000000000000 : ℝ)*(sp5) + (838487933505853/20000000000000 : ℝ)*(sp6) + (1912136185238047/100000000000000 : ℝ)*(sp7) + (1246226641/50000000000000 : ℝ)*(sp12) + (47803419335313/2500000000000 : ℝ)*(f.failure) + (2096222966624603/50000000000000 : ℝ)*(f.sum) + (9881197288699/2817500000000000000000000000 : ℝ)*base65 + (1662196504097825307/563500000000000000000000000000000 : ℝ)*base68 + (561390633111325307/563500000000000000000000000000000 : ℝ)*base70 + (1365023190156825307/563500000000000000000000000000000 : ℝ)*base72 + (1892215014853/352187500000000000000000000 : ℝ)*base73 + (7049178625580325307/563500000000000000000000000000000 : ℝ)*base76 + (4820513612628325307/563500000000000000000000000000000 : ℝ)*base78 + (887098813107174693/563500000000000000000000000000000 : ℝ)*base79 + (1953804109057/5635000000000000000000000000 : ℝ)*base82 + (53403/15625000000000000000 : ℝ)*base89 + (53403/15625000000000000000 : ℝ)*base91 + (53403/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1479/2500 : ℝ) ≤ (1666891279776613319408983161/2817500000000000000000000000 : ℝ) := by norm_num
    linear_combination (60788919/100000000000000 : ℝ)*(upper0) + (228860027/100000000000000 : ℝ)*(lower1) + (423328201/100000000000000 : ℝ)*(upper4) + (11267561/10000000000000 : ℝ)*(upper5) + (1557088522870907/50000000000000 : ℝ)*(major0) + (1557088522870907/50000000000000 : ℝ)*(major1) + (1557088522870907/50000000000000 : ℝ)*(major2) + (170040114606401/4000000000000 : ℝ)*(sp0) + (2125493915436279/50000000000000 : ℝ)*(sp1) + (6642187941613/156250000000 : ℝ)*(sp2) + (195762843423151/10000000000000 : ℝ)*(sp3) + (516505541/20000000000000 : ℝ)*(sp6) + (1051297289/50000000000000 : ℝ)*(sp7) + (15034287467/100000000000000 : ℝ)*(sp9) + (244703817103261/12500000000000 : ℝ)*(f.failure) + (170040114606401/4000000000000 : ℝ)*(f.sum) + (11896280295733/2817500000000000000000000000 : ℝ)*base66 + (25344206667682133719/563500000000000000000000000000000 : ℝ)*base67 + (1336100595788133719/563500000000000000000000000000000 : ℝ)*base69 + (2186266623152366281/563500000000000000000000000000000 : ℝ)*base72 + (70959255069107/2817500000000000000000000000 : ℝ)*base73 + (2201285272528866281/563500000000000000000000000000000 : ℝ)*base76 + (1790613237514633719/563500000000000000000000000000000 : ℝ)*base77 + (3377337403187866281/563500000000000000000000000000000 : ℝ)*base80 + (10159417217503/2817500000000000000000000000 : ℝ)*base82 + (179991/78125000000000000000 : ℝ)*base89 + (179991/78125000000000000000 : ℝ)*base91 + (179991/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40287/50000 : ℝ) ≤ (454050474040768946135834559249249/563500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20768221/100000000000000 : ℝ)*(upper0) + (17376539/100000000000000 : ℝ)*(lower3) + (29169727/100000000000000 : ℝ)*(upper4) + (3420770739925161/100000000000000 : ℝ)*(major0) + (3420770739925161/100000000000000 : ℝ)*(major1) + (1710385369962581/50000000000000 : ℝ)*(major2) + (1483474823/100000000000000 : ℝ)*(sp0) + (16463809031/100000000000000 : ℝ)*(sp1) + (8958598729/50000000000000 : ℝ)*(sp3) + (932863805637293/20000000000000 : ℝ)*(sp8) + (291519059006117/6250000000000 : ℝ)*(sp9) + (4664321407906903/100000000000000 : ℝ)*(sp10) + (1075171604612233/50000000000000 : ℝ)*(sp11) + (56015351/6250000000000 : ℝ)*(sp12) + (537590281605481/25000000000000 : ℝ)*(f.failure) + (4664321407906903/100000000000000 : ℝ)*(f.sum) + (51814560911277/11270000000000000000000000000 : ℝ)*base66 + (13392768586646951363/1127000000000000000000000000000000 : ℝ)*base68 + (3793208666764432777/563500000000000000000000000000000 : ℝ)*base69 + (5975854658271951363/1127000000000000000000000000000000 : ℝ)*base72 + (15667300100987/11270000000000000000000000000 : ℝ)*base74 + (2533769309661932777/563500000000000000000000000000000 : ℝ)*base75 + (250737716875564091/161000000000000000000000000000000 : ℝ)*base77 + (488538549657435909/161000000000000000000000000000000 : ℝ)*base80 + (128568719927/50312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1811/156250000000000000000 : ℝ)*base89 + (1811/156250000000000000000 : ℝ)*base91 + (1560689/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84771/100000 : ℝ) ≤ (-6823829713288397700008381707011/8050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2863679/10000000000000 : ℝ)*(lower0) + (36461999/25000000000000 : ℝ)*(upper3) + (35789823/100000000000000 : ℝ)*(lower4) + (345851964421173/10000000000000 : ℝ)*(major0) + (345851964421173/10000000000000 : ℝ)*(major1) + (345851964421173/10000000000000 : ℝ)*(major2) + (6030252791/100000000000000 : ℝ)*(sp0) + (112432971613/100000000000000 : ℝ)*(sp5) + (7466991767/12500000000000 : ℝ)*(sp6) + (51624333963/100000000000000 : ℝ)*(sp7) + (4771198480863767/100000000000000 : ℝ)*(sp12) + (2385546039072473/50000000000000 : ℝ)*(sp13) + (4771144775182423/100000000000000 : ℝ)*(sp14) + (54350979415761/2500000000000 : ℝ)*(sp15) + (2174090800964403/100000000000000 : ℝ)*(f.failure) + (4771204511116559/100000000000000 : ℝ)*(f.sum) + (262036808293/161000000000000000000000000 : ℝ)*base65 + (58340158615897663/16100000000000000000000000000000 : ℝ)*base67 + (67621689202197663/16100000000000000000000000000000 : ℝ)*base69 + (115446112786902337/16100000000000000000000000000000 : ℝ)*base72 + (32274151541/5031250000000000000000000 : ℝ)*base73 + (146994723321602337/16100000000000000000000000000000 : ℝ)*base76 + (87698523592402337/16100000000000000000000000000000 : ℝ)*base78 + (20277649165202337/16100000000000000000000000000000 : ℝ)*base80 + (374798415431/161000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2216307/625000000000000000000 : ℝ)*base90 + (2216307/625000000000000000000 : ℝ)*base92 + (2216307/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1452_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11387/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31457/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1479/2500 : ℝ) else (40287/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84771/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1452_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1452_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31457/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1479/2500 : ℝ) else (40287/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84771/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1452_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1452_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1452_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4411/1024 : ℝ) ≤ p) (hpb : p ≤ (1103/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9942431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3693/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31457/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(1479/2500 : ℝ) else (40287/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84771/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1452_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
