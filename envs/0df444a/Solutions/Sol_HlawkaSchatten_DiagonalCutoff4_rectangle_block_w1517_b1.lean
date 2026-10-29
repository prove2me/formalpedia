-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1517_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:30.291838+00:00
-- url     : https://prove2.me/submissions/281efe84-9673-47d3-a177-6d46491743a7

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
theorem support_rectangle_w1517_s3_0 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1860185097/10000000000 : ℝ)*x 0 + (2717838333/5000000000 : ℝ)*x 1 + (651887939/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1860185097/10000000000 : ℝ)^4531 ≤ (11383497696037/100000000000000 : ℝ)^3507 := by
    have hnat : (1860185097 : ℕ)^4531*100000000000000^3507 ≤ 11383497696037^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860185097 10000000000 11383497696037 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717838333/5000000000 : ℝ)^4531 ≤ (11373418015087/25000000000000 : ℝ)^3507 := by
    have hnat : (2717838333 : ℕ)^4531*25000000000000^3507 ≤ 11373418015087^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717838333 5000000000 11373418015087 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651887939/1250000000 : ℝ)^4531 ≤ (8624566046483/20000000000000 : ℝ)^3507 := by
    have hnat : (651887939 : ℕ)^4531*20000000000000^3507 ≤ 8624566046483^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651887939 1250000000 8624566046483 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1860185097/10000000000 : ℝ), (2717838333/5000000000 : ℝ), (651887939/1250000000 : ℝ)] ![(11383497696037/100000000000000 : ℝ), (11373418015087/25000000000000 : ℝ), (8624566046483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1860185097/10000000000 : ℝ)|^4531 ≤ (11383497696037/100000000000000 : ℝ)^3507
        have hw : |(-1860185097/10000000000 : ℝ)|=(1860185097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717838333/5000000000 : ℝ)|^4531 ≤ (11373418015087/25000000000000 : ℝ)^3507
        have hw : |(2717838333/5000000000 : ℝ)|=(2717838333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651887939/1250000000 : ℝ)|^4531 ≤ (8624566046483/20000000000000 : ℝ)^3507
        have hw : |(651887939/1250000000 : ℝ)|=(651887939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_1 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676060849/5000000000 : ℝ)*x 0 + (-1973213419/10000000000 : ℝ)*x 1 + (1303775943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676060849/5000000000 : ℝ)^4531 ≤ (8918441497301/20000000000000 : ℝ)^3507 := by
    have hnat : (2676060849 : ℕ)^4531*20000000000000^3507 ≤ 8918441497301^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676060849 5000000000 8918441497301 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973213419/10000000000 : ℝ)^4531 ≤ (12284959493193/100000000000000 : ℝ)^3507 := by
    have hnat : (1973213419 : ℕ)^4531*100000000000000^3507 ≤ 12284959493193^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973213419 10000000000 12284959493193 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303775943/2500000000 : ℝ)^4531 ≤ (8624566602011/20000000000000 : ℝ)^3507 := by
    have hnat : (1303775943 : ℕ)^4531*20000000000000^3507 ≤ 8624566602011^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303775943 2500000000 8624566602011 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676060849/5000000000 : ℝ), (-1973213419/10000000000 : ℝ), (1303775943/2500000000 : ℝ)] ![(8918441497301/20000000000000 : ℝ), (12284959493193/100000000000000 : ℝ), (8624566602011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676060849/5000000000 : ℝ)|^4531 ≤ (8918441497301/20000000000000 : ℝ)^3507
        have hw : |(2676060849/5000000000 : ℝ)|=(2676060849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973213419/10000000000 : ℝ)|^4531 ≤ (12284959493193/100000000000000 : ℝ)^3507
        have hw : |(-1973213419/10000000000 : ℝ)|=(1973213419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303775943/2500000000 : ℝ)|^4531 ≤ (8624566602011/20000000000000 : ℝ)^3507
        have hw : |(1303775943/2500000000 : ℝ)|=(1303775943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_2 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676060893/5000000000 : ℝ)*x 0 + (2607551837/5000000000 : ℝ)*x 1 + (-246651679/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676060893/5000000000 : ℝ)^4531 ≤ (1783688337351/4000000000000 : ℝ)^3507 := by
    have hnat : (2676060893 : ℕ)^4531*4000000000000^3507 ≤ 1783688337351^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676060893 5000000000 1783688337351 4000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607551837/5000000000 : ℝ)^4531 ≤ (21561415981549/50000000000000 : ℝ)^3507 := by
    have hnat : (2607551837 : ℕ)^4531*50000000000000^3507 ≤ 21561415981549^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607551837 5000000000 21561415981549 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246651679/1250000000 : ℝ)^4531 ≤ (6142479798881/50000000000000 : ℝ)^3507 := by
    have hnat : (246651679 : ℕ)^4531*50000000000000^3507 ≤ 6142479798881^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246651679 1250000000 6142479798881 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676060893/5000000000 : ℝ), (2607551837/5000000000 : ℝ), (-246651679/1250000000 : ℝ)] ![(1783688337351/4000000000000 : ℝ), (21561415981549/50000000000000 : ℝ), (6142479798881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676060893/5000000000 : ℝ)|^4531 ≤ (1783688337351/4000000000000 : ℝ)^3507
        have hw : |(2676060893/5000000000 : ℝ)|=(2676060893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607551837/5000000000 : ℝ)|^4531 ≤ (21561415981549/50000000000000 : ℝ)^3507
        have hw : |(2607551837/5000000000 : ℝ)|=(2607551837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246651679/1250000000 : ℝ)|^4531 ≤ (6142479798881/50000000000000 : ℝ)^3507
        have hw : |(-246651679/1250000000 : ℝ)|=(246651679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_3 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133577817/5000000000 : ℝ)*x 0 + (804485761/2000000000 : ℝ)*x 1 + (4524360301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133577817/5000000000 : ℝ)^4531 ≤ (33276953542879/100000000000000 : ℝ)^3507 := by
    have hnat : (2133577817 : ℕ)^4531*100000000000000^3507 ≤ 33276953542879^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133577817 5000000000 33276953542879 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804485761/2000000000 : ℝ)^4531 ≤ (30832158587819/100000000000000 : ℝ)^3507 := by
    have hnat : (804485761 : ℕ)^4531*100000000000000^3507 ≤ 30832158587819^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804485761 2000000000 30832158587819 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524360301/10000000000 : ℝ)^4531 ≤ (35890887861057/100000000000000 : ℝ)^3507 := by
    have hnat : (4524360301 : ℕ)^4531*100000000000000^3507 ≤ 35890887861057^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524360301 10000000000 35890887861057 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133577817/5000000000 : ℝ), (804485761/2000000000 : ℝ), (4524360301/10000000000 : ℝ)] ![(33276953542879/100000000000000 : ℝ), (30832158587819/100000000000000 : ℝ), (35890887861057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133577817/5000000000 : ℝ)|^4531 ≤ (33276953542879/100000000000000 : ℝ)^3507
        have hw : |(2133577817/5000000000 : ℝ)|=(2133577817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804485761/2000000000 : ℝ)|^4531 ≤ (30832158587819/100000000000000 : ℝ)^3507
        have hw : |(804485761/2000000000 : ℝ)|=(804485761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524360301/10000000000 : ℝ)|^4531 ≤ (35890887861057/100000000000000 : ℝ)^3507
        have hw : |(4524360301/10000000000 : ℝ)|=(4524360301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_4 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-930108053/5000000000 : ℝ)*x 0 + (5216271069/10000000000 : ℝ)*x 1 + (2717250199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930108053/5000000000 : ℝ)^4531 ≤ (1138374286567/10000000000000 : ℝ)^3507 := by
    have hnat : (930108053 : ℕ)^4531*10000000000000^3507 ≤ 1138374286567^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930108053 5000000000 1138374286567 10000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216271069/10000000000 : ℝ)^4531 ≤ (43135303921247/100000000000000 : ℝ)^3507 := by
    have hnat : (5216271069 : ℕ)^4531*100000000000000^3507 ≤ 43135303921247^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216271069 10000000000 43135303921247 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717250199/5000000000 : ℝ)^4531 ≤ (45480953198957/100000000000000 : ℝ)^3507 := by
    have hnat : (2717250199 : ℕ)^4531*100000000000000^3507 ≤ 45480953198957^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717250199 5000000000 45480953198957 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930108053/5000000000 : ℝ), (5216271069/10000000000 : ℝ), (2717250199/5000000000 : ℝ)] ![(1138374286567/10000000000000 : ℝ), (43135303921247/100000000000000 : ℝ), (45480953198957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930108053/5000000000 : ℝ)|^4531 ≤ (1138374286567/10000000000000 : ℝ)^3507
        have hw : |(-930108053/5000000000 : ℝ)|=(930108053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216271069/10000000000 : ℝ)|^4531 ≤ (43135303921247/100000000000000 : ℝ)^3507
        have hw : |(5216271069/10000000000 : ℝ)|=(5216271069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717250199/5000000000 : ℝ)|^4531 ≤ (45480953198957/100000000000000 : ℝ)^3507
        have hw : |(2717250199/5000000000 : ℝ)|=(2717250199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_5 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661771777/1250000000 : ℝ)*x 0 + (-219227009/1250000000 : ℝ)*x 1 + (339656283/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661771777/1250000000 : ℝ)^4531 ≤ (21984712012673/50000000000000 : ℝ)^3507 := by
    have hnat : (661771777 : ℕ)^4531*50000000000000^3507 ≤ 21984712012673^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661771777 1250000000 21984712012673 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219227009/1250000000 : ℝ)^4531 ≤ (10549621352571/100000000000000 : ℝ)^3507 := by
    have hnat : (219227009 : ℕ)^4531*100000000000000^3507 ≤ 10549621352571^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219227009 1250000000 10549621352571 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339656283/625000000 : ℝ)^4531 ≤ (11370238651147/25000000000000 : ℝ)^3507 := by
    have hnat : (339656283 : ℕ)^4531*25000000000000^3507 ≤ 11370238651147^3507*625000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339656283 625000000 11370238651147 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661771777/1250000000 : ℝ), (-219227009/1250000000 : ℝ), (339656283/625000000 : ℝ)] ![(21984712012673/50000000000000 : ℝ), (10549621352571/100000000000000 : ℝ), (11370238651147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661771777/1250000000 : ℝ)|^4531 ≤ (21984712012673/50000000000000 : ℝ)^3507
        have hw : |(661771777/1250000000 : ℝ)|=(661771777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219227009/1250000000 : ℝ)|^4531 ≤ (10549621352571/100000000000000 : ℝ)^3507
        have hw : |(-219227009/1250000000 : ℝ)|=(219227009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339656283/625000000 : ℝ)|^4531 ≤ (11370238651147/25000000000000 : ℝ)^3507
        have hw : |(339656283/625000000 : ℝ)|=(339656283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_6 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52941743/100000000 : ℝ)*x 0 + (679312537/1250000000 : ℝ)*x 1 + (-43845407/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52941743/100000000 : ℝ)^4531 ≤ (43969424926689/100000000000000 : ℝ)^3507 := by
    have hnat : (52941743 : ℕ)^4531*100000000000000^3507 ≤ 43969424926689^3507*100000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52941743 100000000 43969424926689 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679312537/1250000000 : ℝ)^4531 ≤ (11370238024019/25000000000000 : ℝ)^3507 := by
    have hnat : (679312537 : ℕ)^4531*25000000000000^3507 ≤ 11370238024019^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679312537 1250000000 11370238024019 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43845407/250000000 : ℝ)^4531 ≤ (5274811484533/50000000000000 : ℝ)^3507 := by
    have hnat : (43845407 : ℕ)^4531*50000000000000^3507 ≤ 5274811484533^3507*250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43845407 250000000 5274811484533 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52941743/100000000 : ℝ), (679312537/1250000000 : ℝ), (-43845407/250000000 : ℝ)] ![(43969424926689/100000000000000 : ℝ), (11370238024019/25000000000000 : ℝ), (5274811484533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52941743/100000000 : ℝ)|^4531 ≤ (43969424926689/100000000000000 : ℝ)^3507
        have hw : |(52941743/100000000 : ℝ)|=(52941743/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679312537/1250000000 : ℝ)|^4531 ≤ (11370238024019/25000000000000 : ℝ)^3507
        have hw : |(679312537/1250000000 : ℝ)|=(679312537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43845407/250000000 : ℝ)|^4531 ≤ (5274811484533/50000000000000 : ℝ)^3507
        have hw : |(-43845407/250000000 : ℝ)|=(43845407/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s3_7 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133613393/5000000000 : ℝ)*x 0 + (565212947/1250000000 : ℝ)*x 1 + (2012552723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133613393/5000000000 : ℝ)^4531 ≤ (16638835215631/50000000000000 : ℝ)^3507 := by
    have hnat : (2133613393 : ℕ)^4531*50000000000000^3507 ≤ 16638835215631^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133613393 5000000000 16638835215631 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565212947/1250000000 : ℝ)^4531 ≤ (8965915295379/25000000000000 : ℝ)^3507 := by
    have hnat : (565212947 : ℕ)^4531*25000000000000^3507 ≤ 8965915295379^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565212947 1250000000 8965915295379 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012552723/5000000000 : ℝ)^4531 ≤ (30858668370641/100000000000000 : ℝ)^3507 := by
    have hnat : (2012552723 : ℕ)^4531*100000000000000^3507 ≤ 30858668370641^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012552723 5000000000 30858668370641 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133613393/5000000000 : ℝ), (565212947/1250000000 : ℝ), (2012552723/5000000000 : ℝ)] ![(16638835215631/50000000000000 : ℝ), (8965915295379/25000000000000 : ℝ), (30858668370641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133613393/5000000000 : ℝ)|^4531 ≤ (16638835215631/50000000000000 : ℝ)^3507
        have hw : |(2133613393/5000000000 : ℝ)|=(2133613393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565212947/1250000000 : ℝ)|^4531 ≤ (8965915295379/25000000000000 : ℝ)^3507
        have hw : |(565212947/1250000000 : ℝ)|=(565212947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012552723/5000000000 : ℝ)|^4531 ≤ (30858668370641/100000000000000 : ℝ)^3507
        have hw : |(2012552723/5000000000 : ℝ)|=(2012552723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1517_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7989/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (2719/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15547/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7989/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (131/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7989/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (131/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7989/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (131/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7989/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (131/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7989/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (131/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7989/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (131/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (131/1250 : ℝ) ^ (4529/1024 : ℝ) ≤ (4647328460070317/100000000000000000000 : ℝ) := by
    have hpowers : (131/1250 : ℝ)^4529 ≤ (4647328460070317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (131 : ℕ)^4529*100000000000000000000^1024 ≤ 4647328460070317^1024*1250^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        131 1250 4647328460070317 100000000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (131/1250 : ℝ)) (X := (4647328460070317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7989/50000 : ℝ) ^ (4529/1024 : ℝ) ≤ (750305077467727/2500000000000000000 : ℝ) := by
    have hpowers : (7989/50000 : ℝ)^4529 ≤ (750305077467727/2500000000000000000 : ℝ)^1024 := by
      have hnat : (7989 : ℕ)^4529*2500000000000000000^1024 ≤ 750305077467727^1024*50000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7989 50000 750305077467727 2500000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7989/50000 : ℝ)) (X := (750305077467727/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004647328460070317/50000000000000000000 : ℝ) ≤ (1250026267902387/1250000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (50004647328460070317/50000000000000000000 : ℝ)^1024 ≤ (1250026267902387/1250000000000000 : ℝ)^4529 := by
      have hnat : (50004647328460070317 : ℕ)^1024*1250000000000000^4529 ≤ 1250026267902387^4529*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004647328460070317 50000000000000000000 1250026267902387 1250000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250026267902387/1250000000000000 : ℝ)) (X := (50004647328460070317/50000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034659531558779397/100000000000000000000 : ℝ) ≤ (5000391770825307/5000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (100034659531558779397/100000000000000000000 : ℝ)^1024 ≤ (5000391770825307/5000000000000000 : ℝ)^4529 := by
      have hnat : (100034659531558779397 : ℕ)^1024*5000000000000000^4529 ≤ 5000391770825307^4529*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034659531558779397 100000000000000000000 5000391770825307 5000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000391770825307/5000000000000000 : ℝ)) (X := (100034659531558779397/100000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250750305077467727/1250000000000000000 : ℝ) ≤ (2500339235020533/2500000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (1250750305077467727/1250000000000000000 : ℝ)^1024 ≤ (2500339235020533/2500000000000000 : ℝ)^4529 := by
      have hnat : (1250750305077467727 : ℕ)^1024*2500000000000000^4529 ≤ 2500339235020533^4529*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250750305077467727 1250000000000000000 2500339235020533 2500000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500339235020533/2500000000000000 : ℝ)) (X := (1250750305077467727/1250000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4647328460070317/100000000000000000000 : ℝ) ≤ ((3435571058518373283/3436250000000000000 : ℝ)+2*(286699215759/274900000000000 : ℝ)*(131/1250 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (3435571058518373283/3436250000000000000 : ℝ)+2*(286699215759/274900000000000 : ℝ)*(131/1250 : ℝ)=(1250026267902387/1250000000000000 : ℝ) by norm_num, show 1+2*(4647328460070317/100000000000000000000 : ℝ)=(50004647328460070317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(750305077467727/2500000000000000000 : ℝ)+(4647328460070317/100000000000000000000 : ℝ) ≤ ((3435571058518373283/3436250000000000000 : ℝ)+(286699215759/274900000000000 : ℝ)*((7989/50000 : ℝ)+(131/1250 : ℝ)))^(4529/1024 : ℝ) := by
    rw [show (3435571058518373283/3436250000000000000 : ℝ)+(286699215759/274900000000000 : ℝ)*((7989/50000 : ℝ)+(131/1250 : ℝ))=(5000391770825307/5000000000000000 : ℝ) by norm_num, show 1+(750305077467727/2500000000000000000 : ℝ)+(4647328460070317/100000000000000000000 : ℝ)=(100034659531558779397/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(750305077467727/2500000000000000000 : ℝ) ≤ ((3435571058518373283/3436250000000000000 : ℝ)+2*(286699215759/274900000000000 : ℝ)*(7989/50000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (3435571058518373283/3436250000000000000 : ℝ)+2*(286699215759/274900000000000 : ℝ)*(7989/50000 : ℝ)=(2500339235020533/2500000000000000 : ℝ) by norm_num, show 1+2*(750305077467727/2500000000000000000 : ℝ)=(1250750305077467727/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3435571058518373283/3436250000000000000 : ℝ)*(X 1 0+X 2 0)+(286699215759/274900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (131/1250 : ℝ)) (hi := (7989/50000 : ℝ)) (c := (3435571058518373283/3436250000000000000 : ℝ)) (alpha := (286699215759/274900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3435571058518373283/3436250000000000000 : ℝ)*(X 0 1+X 2 1)+(286699215759/274900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (131/1250 : ℝ)) (hi := (7989/50000 : ℝ)) (c := (3435571058518373283/3436250000000000000 : ℝ)) (alpha := (286699215759/274900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3435571058518373283/3436250000000000000 : ℝ)*(X 0 2+X 1 2)+(286699215759/274900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (131/1250 : ℝ)) (hi := (7989/50000 : ℝ)) (c := (3435571058518373283/3436250000000000000 : ℝ)) (alpha := (286699215759/274900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1860185097/10000000000 : ℝ)*X 0 0+(2717838333/5000000000 : ℝ)*X 0 1+(651887939/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676060849/5000000000 : ℝ)*X 1 0+(-1973213419/10000000000 : ℝ)*X 1 1+(1303775943/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676060893/5000000000 : ℝ)*X 2 0+(2607551837/5000000000 : ℝ)*X 2 1+(-246651679/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133577817/5000000000 : ℝ)*X 0 0+(804485761/2000000000 : ℝ)*X 0 1+(4524360301/10000000000 : ℝ)*X 0 2+(2133577817/5000000000 : ℝ)*X 1 0+(804485761/2000000000 : ℝ)*X 1 1+(4524360301/10000000000 : ℝ)*X 1 2+(2133577817/5000000000 : ℝ)*X 2 0+(804485761/2000000000 : ℝ)*X 2 1+(4524360301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-930108053/5000000000 : ℝ)*X 0 0+(5216271069/10000000000 : ℝ)*X 0 1+(2717250199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661771777/1250000000 : ℝ)*X 1 0+(-219227009/1250000000 : ℝ)*X 1 1+(339656283/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((52941743/100000000 : ℝ)*X 2 0+(679312537/1250000000 : ℝ)*X 2 1+(-43845407/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133613393/5000000000 : ℝ)*X 0 0+(565212947/1250000000 : ℝ)*X 0 1+(2012552723/5000000000 : ℝ)*X 0 2+(2133613393/5000000000 : ℝ)*X 1 0+(565212947/1250000000 : ℝ)*X 1 1+(2012552723/5000000000 : ℝ)*X 1 2+(2133613393/5000000000 : ℝ)*X 2 0+(565212947/1250000000 : ℝ)*X 2 1+(2012552723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13634534178710351763349401/5369140625000000000000000000000 : ℝ) := by norm_num
    linear_combination (44402603/20000000000000 : ℝ)*(base19) + (9197213/3125000000000 : ℝ)*(base23) + (50060161/50000000000000 : ℝ)*(upper3) + (120149/10000000000000 : ℝ)*(upper4) + (98606509/100000000000000 : ℝ)*(upper5) + (815745522891961/25000000000000 : ℝ)*(major0) + (815745522891961/25000000000000 : ℝ)*(major1) + (815745522891961/25000000000000 : ℝ)*(major2) + (906729701145343/20000000000000 : ℝ)*(sp0) + (4533653934915571/100000000000000 : ℝ)*(sp1) + (453365386261777/10000000000000 : ℝ)*(sp2) + (996153364256447/50000000000000 : ℝ)*(sp3) + (5651201871/100000000000000 : ℝ)*(sp4) + (3213046677/100000000000000 : ℝ)*(sp7) + (1992309941559571/100000000000000 : ℝ)*(f.failure) + (2266827078464293/50000000000000 : ℝ)*(f.sum) + (9657182366031/13745000000000000000000000000 : ℝ)*base65 + (235956835197271713/85906250000000000000000000000000 : ℝ)*base67 + (683402900435177963/85906250000000000000000000000000 : ℝ)*base69 + (1016366702691490463/85906250000000000000000000000000 : ℝ)*base71 + (70186796018289/13745000000000000000000000000 : ℝ)*base74 + (151895255515615463/85906250000000000000000000000000 : ℝ)*base75 + (117737702915302963/85906250000000000000000000000000 : ℝ)*base77 + (518555350336052963/85906250000000000000000000000000 : ℝ)*base79 + (4588240555697/1718125000000000000000000000 : ℝ)*base81 + (12281931/10000000000000000000000 : ℝ)*base90 + (12281931/10000000000000000000000 : ℝ)*base92 + (12281931/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (896627477398156407435995817/171812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135348023/10000000000000 : ℝ)*(base19) + (1696838681/100000000000000 : ℝ)*(base23) + (44736751/25000000000000 : ℝ)*(upper3) + (133758889/100000000000000 : ℝ)*(lower4) + (94659073/100000000000000 : ℝ)*(upper5) + (3298016053326411/100000000000000 : ℝ)*(major0) + (3298016053326411/100000000000000 : ℝ)*(major1) + (3298016053326411/100000000000000 : ℝ)*(major2) + (710121351/3125000000000 : ℝ)*(sp1) + (4873677273/20000000000000 : ℝ)*(sp2) + (2291165486316553/50000000000000 : ℝ)*(sp4) + (1145576723817411/25000000000000 : ℝ)*(sp5) + (229115245370403/5000000000000 : ℝ)*(sp6) + (1006850480032531/50000000000000 : ℝ)*(sp7) + (1006850480032531/50000000000000 : ℝ)*(f.failure) + (2291165486316553/50000000000000 : ℝ)*(f.sum) + (86657012731571/13745000000000000000000000000 : ℝ)*base66 + (2901678595806710187/343625000000000000000000000000000 : ℝ)*base68 + (5458878052892460187/343625000000000000000000000000000 : ℝ)*base70 + (1761099852775960187/343625000000000000000000000000000 : ℝ)*base72 + (39738560243371/13745000000000000000000000000 : ℝ)*base74 + (4443860297898960187/343625000000000000000000000000000 : ℝ)*base76 + (3207362102607210187/343625000000000000000000000000000 : ℝ)*base78 + (1062041079999710187/343625000000000000000000000000000 : ℝ)*base80 + (85234551973191/13745000000000000000000000000 : ℝ)*base82 + (59411509/5000000000000000000000 : ℝ)*base89 + (59411509/5000000000000000000000 : ℝ)*base91 + (59411509/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1517_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7989/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15547/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1517_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1517_s4_0 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1860599957/10000000000 : ℝ)*x 0 + (5432950567/10000000000 : ℝ)*x 1 + (2608777689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1860599957/10000000000 : ℝ)^4531 ≤ (11386777844963/100000000000000 : ℝ)^3507 := by
    have hnat : (1860599957 : ℕ)^4531*100000000000000^3507 ≤ 11386777844963^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860599957 10000000000 11386777844963 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432950567/10000000000 : ℝ)^4531 ≤ (1136604906691/2500000000000 : ℝ)^3507 := by
    have hnat : (5432950567 : ℕ)^4531*2500000000000^3507 ≤ 1136604906691^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432950567 10000000000 1136604906691 2500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608777689/5000000000 : ℝ)^4531 ≤ (21574512940519/50000000000000 : ℝ)^3507 := by
    have hnat : (2608777689 : ℕ)^4531*50000000000000^3507 ≤ 21574512940519^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608777689 5000000000 21574512940519 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1860599957/10000000000 : ℝ), (5432950567/10000000000 : ℝ), (2608777689/5000000000 : ℝ)] ![(11386777844963/100000000000000 : ℝ), (1136604906691/2500000000000 : ℝ), (21574512940519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1860599957/10000000000 : ℝ)|^4531 ≤ (11386777844963/100000000000000 : ℝ)^3507
        have hw : |(-1860599957/10000000000 : ℝ)|=(1860599957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432950567/10000000000 : ℝ)|^4531 ≤ (1136604906691/2500000000000 : ℝ)^3507
        have hw : |(5432950567/10000000000 : ℝ)|=(5432950567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608777689/5000000000 : ℝ)|^4531 ≤ (21574512940519/50000000000000 : ℝ)^3507
        have hw : |(2608777689/5000000000 : ℝ)|=(2608777689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_1 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535140733/1000000000 : ℝ)*x 0 + (-985456183/5000000000 : ℝ)*x 1 + (5217555627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535140733/1000000000 : ℝ)^4531 ≤ (44584517867589/100000000000000 : ℝ)^3507 := by
    have hnat : (535140733 : ℕ)^4531*100000000000000^3507 ≤ 44584517867589^3507*1000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535140733 1000000000 44584517867589 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985456183/5000000000 : ℝ)^4531 ≤ (12266453575703/100000000000000 : ℝ)^3507 := by
    have hnat : (985456183 : ℕ)^4531*100000000000000^3507 ≤ 12266453575703^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985456183 5000000000 12266453575703 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217555627/10000000000 : ℝ)^4531 ≤ (5393628567691/12500000000000 : ℝ)^3507 := by
    have hnat : (5217555627 : ℕ)^4531*12500000000000^3507 ≤ 5393628567691^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217555627 10000000000 5393628567691 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535140733/1000000000 : ℝ), (-985456183/5000000000 : ℝ), (5217555627/10000000000 : ℝ)] ![(44584517867589/100000000000000 : ℝ), (12266453575703/100000000000000 : ℝ), (5393628567691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535140733/1000000000 : ℝ)|^4531 ≤ (44584517867589/100000000000000 : ℝ)^3507
        have hw : |(535140733/1000000000 : ℝ)|=(535140733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985456183/5000000000 : ℝ)|^4531 ≤ (12266453575703/100000000000000 : ℝ)^3507
        have hw : |(-985456183/5000000000 : ℝ)|=(985456183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217555627/10000000000 : ℝ)|^4531 ≤ (5393628567691/12500000000000 : ℝ)^3507
        have hw : |(5217555627/10000000000 : ℝ)|=(5217555627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_2 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351407521/10000000000 : ℝ)*x 0 + (5217555463/10000000000 : ℝ)*x 1 + (-1970912329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351407521/10000000000 : ℝ)^4531 ≤ (11146129980879/25000000000000 : ℝ)^3507 := by
    have hnat : (5351407521 : ℕ)^4531*25000000000000^3507 ≤ 11146129980879^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351407521 10000000000 11146129980879 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217555463/10000000000 : ℝ)^4531 ≤ (43149026789237/100000000000000 : ℝ)^3507 := by
    have hnat : (5217555463 : ℕ)^4531*100000000000000^3507 ≤ 43149026789237^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217555463 10000000000 43149026789237 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970912329/10000000000 : ℝ)^4531 ≤ (6133226639093/50000000000000 : ℝ)^3507 := by
    have hnat : (1970912329 : ℕ)^4531*50000000000000^3507 ≤ 6133226639093^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970912329 10000000000 6133226639093 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351407521/10000000000 : ℝ), (5217555463/10000000000 : ℝ), (-1970912329/10000000000 : ℝ)] ![(11146129980879/25000000000000 : ℝ), (43149026789237/100000000000000 : ℝ), (6133226639093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351407521/10000000000 : ℝ)|^4531 ≤ (11146129980879/25000000000000 : ℝ)^3507
        have hw : |(5351407521/10000000000 : ℝ)|=(5351407521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217555463/10000000000 : ℝ)|^4531 ≤ (43149026789237/100000000000000 : ℝ)^3507
        have hw : |(5217555463/10000000000 : ℝ)|=(5217555463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970912329/10000000000 : ℝ)|^4531 ≤ (6133226639093/50000000000000 : ℝ)^3507
        have hw : |(-1970912329/10000000000 : ℝ)|=(1970912329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_3 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853482951/2000000000 : ℝ)*x 0 + (4028290909/10000000000 : ℝ)*x 1 + (2259219493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853482951/2000000000 : ℝ)^4531 ≤ (1663978216011/5000000000000 : ℝ)^3507 := by
    have hnat : (853482951 : ℕ)^4531*5000000000000^3507 ≤ 1663978216011^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853482951 2000000000 1663978216011 5000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028290909/10000000000 : ℝ)^4531 ≤ (6178044859579/20000000000000 : ℝ)^3507 := by
    have hnat : (4028290909 : ℕ)^4531*20000000000000^3507 ≤ 6178044859579^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028290909 10000000000 6178044859579 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259219493/5000000000 : ℝ)^4531 ≤ (17915105684427/50000000000000 : ℝ)^3507 := by
    have hnat : (2259219493 : ℕ)^4531*50000000000000^3507 ≤ 17915105684427^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259219493 5000000000 17915105684427 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853482951/2000000000 : ℝ), (4028290909/10000000000 : ℝ), (2259219493/5000000000 : ℝ)] ![(1663978216011/5000000000000 : ℝ), (6178044859579/20000000000000 : ℝ), (17915105684427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853482951/2000000000 : ℝ)|^4531 ≤ (1663978216011/5000000000000 : ℝ)^3507
        have hw : |(853482951/2000000000 : ℝ)|=(853482951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028290909/10000000000 : ℝ)|^4531 ≤ (6178044859579/20000000000000 : ℝ)^3507
        have hw : |(4028290909/10000000000 : ℝ)|=(4028290909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259219493/5000000000 : ℝ)|^4531 ≤ (17915105684427/50000000000000 : ℝ)^3507
        have hw : |(2259219493/5000000000 : ℝ)|=(2259219493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_4 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-37212571/200000000 : ℝ)*x 0 + (5218669189/10000000000 : ℝ)*x 1 + (1086365771/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37212571/200000000 : ℝ)^4531 ≤ (5693501963703/50000000000000 : ℝ)^3507 := by
    have hnat : (37212571 : ℕ)^4531*50000000000000^3507 ≤ 5693501963703^3507*200000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37212571 200000000 5693501963703 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218669189/10000000000 : ℝ)^4531 ≤ (21580463492673/50000000000000 : ℝ)^3507 := by
    have hnat : (5218669189 : ℕ)^4531*50000000000000^3507 ≤ 21580463492673^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218669189 10000000000 21580463492673 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086365771/2000000000 : ℝ)^4531 ≤ (22726034536681/50000000000000 : ℝ)^3507 := by
    have hnat : (1086365771 : ℕ)^4531*50000000000000^3507 ≤ 22726034536681^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086365771 2000000000 22726034536681 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37212571/200000000 : ℝ), (5218669189/10000000000 : ℝ), (1086365771/2000000000 : ℝ)] ![(5693501963703/50000000000000 : ℝ), (21580463492673/50000000000000 : ℝ), (22726034536681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37212571/200000000 : ℝ)|^4531 ≤ (5693501963703/50000000000000 : ℝ)^3507
        have hw : |(-37212571/200000000 : ℝ)|=(37212571/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218669189/10000000000 : ℝ)|^4531 ≤ (21580463492673/50000000000000 : ℝ)^3507
        have hw : |(5218669189/10000000000 : ℝ)|=(5218669189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086365771/2000000000 : ℝ)|^4531 ≤ (22726034536681/50000000000000 : ℝ)^3507
        have hw : |(1086365771/2000000000 : ℝ)|=(1086365771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_5 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294821049/10000000000 : ℝ)*x 0 + (-1756638729/10000000000 : ℝ)*x 1 + (5431829129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294821049/10000000000 : ℝ)^4531 ≤ (43976364844987/100000000000000 : ℝ)^3507 := by
    have hnat : (5294821049 : ℕ)^4531*100000000000000^3507 ≤ 43976364844987^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294821049 10000000000 43976364844987 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1756638729/10000000000 : ℝ)^4531 ≤ (528578155033/5000000000000 : ℝ)^3507 := by
    have hnat : (1756638729 : ℕ)^4531*5000000000000^3507 ≤ 528578155033^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756638729 10000000000 528578155033 5000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431829129/10000000000 : ℝ)^4531 ≤ (5681509004447/12500000000000 : ℝ)^3507 := by
    have hnat : (5431829129 : ℕ)^4531*12500000000000^3507 ≤ 5681509004447^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431829129 10000000000 5681509004447 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294821049/10000000000 : ℝ), (-1756638729/10000000000 : ℝ), (5431829129/10000000000 : ℝ)] ![(43976364844987/100000000000000 : ℝ), (528578155033/5000000000000 : ℝ), (5681509004447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294821049/10000000000 : ℝ)|^4531 ≤ (43976364844987/100000000000000 : ℝ)^3507
        have hw : |(5294821049/10000000000 : ℝ)|=(5294821049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1756638729/10000000000 : ℝ)|^4531 ≤ (528578155033/5000000000000 : ℝ)^3507
        have hw : |(-1756638729/10000000000 : ℝ)|=(1756638729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431829129/10000000000 : ℝ)|^4531 ≤ (5681509004447/12500000000000 : ℝ)^3507
        have hw : |(5431829129/10000000000 : ℝ)|=(5431829129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_6 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294820973/10000000000 : ℝ)*x 0 + (5431829253/10000000000 : ℝ)*x 1 + (-1756638661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294820973/10000000000 : ℝ)^4531 ≤ (43976364029457/100000000000000 : ℝ)^3507 := by
    have hnat : (5294820973 : ℕ)^4531*100000000000000^3507 ≤ 43976364029457^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294820973 10000000000 43976364029457 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431829253/10000000000 : ℝ)^4531 ≤ (45452073376141/100000000000000 : ℝ)^3507 := by
    have hnat : (5431829253 : ℕ)^4531*100000000000000^3507 ≤ 45452073376141^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431829253 10000000000 45452073376141 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1756638661/10000000000 : ℝ)^4531 ≤ (5285781285971/50000000000000 : ℝ)^3507 := by
    have hnat : (1756638661 : ℕ)^4531*50000000000000^3507 ≤ 5285781285971^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756638661 10000000000 5285781285971 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294820973/10000000000 : ℝ), (5431829253/10000000000 : ℝ), (-1756638661/10000000000 : ℝ)] ![(43976364029457/100000000000000 : ℝ), (45452073376141/100000000000000 : ℝ), (5285781285971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294820973/10000000000 : ℝ)|^4531 ≤ (43976364029457/100000000000000 : ℝ)^3507
        have hw : |(5294820973/10000000000 : ℝ)|=(5294820973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431829253/10000000000 : ℝ)|^4531 ≤ (45452073376141/100000000000000 : ℝ)^3507
        have hw : |(5431829253/10000000000 : ℝ)|=(5431829253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1756638661/10000000000 : ℝ)|^4531 ≤ (5285781285971/50000000000000 : ℝ)^3507
        have hw : |(-1756638661/10000000000 : ℝ)|=(1756638661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s4_7 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133740381/5000000000 : ℝ)*x 0 + (4515905513/10000000000 : ℝ)*x 1 + (251927699/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133740381/5000000000 : ℝ)^4531 ≤ (3328022938209/10000000000000 : ℝ)^3507 := by
    have hnat : (2133740381 : ℕ)^4531*10000000000000^3507 ≤ 3328022938209^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133740381 5000000000 3328022938209 10000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515905513/10000000000 : ℝ)^4531 ≤ (8951064406943/25000000000000 : ℝ)^3507 := by
    have hnat : (4515905513 : ℕ)^4531*25000000000000^3507 ≤ 8951064406943^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515905513 10000000000 8951064406943 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251927699/625000000 : ℝ)^4531 ≤ (15457756488997/50000000000000 : ℝ)^3507 := by
    have hnat : (251927699 : ℕ)^4531*50000000000000^3507 ≤ 15457756488997^3507*625000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251927699 625000000 15457756488997 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133740381/5000000000 : ℝ), (4515905513/10000000000 : ℝ), (251927699/625000000 : ℝ)] ![(3328022938209/10000000000000 : ℝ), (8951064406943/25000000000000 : ℝ), (15457756488997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133740381/5000000000 : ℝ)|^4531 ≤ (3328022938209/10000000000000 : ℝ)^3507
        have hw : |(2133740381/5000000000 : ℝ)|=(2133740381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515905513/10000000000 : ℝ)|^4531 ≤ (8951064406943/25000000000000 : ℝ)^3507
        have hw : |(4515905513/10000000000 : ℝ)|=(4515905513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251927699/625000000 : ℝ)|^4531 ≤ (15457756488997/50000000000000 : ℝ)^3507
        have hw : |(251927699/625000000 : ℝ)|=(251927699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1517_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15547/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (683/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15547/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15547/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2719/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15547/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15547/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2719/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15547/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15547/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2719/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2719/25000 : ℝ) ^ (4529/1024 : ℝ) ≤ (5475783778886693/100000000000000000000 : ℝ) := by
    have hpowers : (2719/25000 : ℝ)^4529 ≤ (5475783778886693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2719 : ℕ)^4529*100000000000000000000^1024 ≤ 5475783778886693^1024*25000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2719 25000 5475783778886693 100000000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2719/25000 : ℝ)) (X := (5475783778886693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15547/100000 : ℝ) ^ (4529/1024 : ℝ) ≤ (5318668113573537/20000000000000000000 : ℝ) := by
    have hpowers : (15547/100000 : ℝ)^4529 ≤ (5318668113573537/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15547 : ℕ)^4529*20000000000000000000^1024 ≤ 5318668113573537^1024*100000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15547 100000 5318668113573537 20000000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15547/100000 : ℝ)) (X := (5318668113573537/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005475783778886693/50000000000000000000 : ℝ) ≤ (10000247602781523/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (50005475783778886693/50000000000000000000 : ℝ)^1024 ≤ (10000247602781523/10000000000000000 : ℝ)^4529 := by
      have hnat : (50005475783778886693 : ℕ)^1024*10000000000000000^4529 ≤ 10000247602781523^4529*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005475783778886693 50000000000000000000 10000247602781523 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000247602781523/10000000000000000 : ℝ)) (X := (50005475783778886693/50000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016034562173377189/50000000000000000000 : ℝ) ≤ (500036249402829/500000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (50016034562173377189/50000000000000000000 : ℝ)^1024 ≤ (500036249402829/500000000000000 : ℝ)^4529 := by
      have hnat : (50016034562173377189 : ℕ)^1024*500000000000000^4529 ≤ 500036249402829^4529*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016034562173377189 50000000000000000000 500036249402829 500000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500036249402829/500000000000000 : ℝ)) (X := (50016034562173377189/50000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005318668113573537/10000000000000000000 : ℝ) ≤ (10001202373331637/10000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (10005318668113573537/10000000000000000000 : ℝ)^1024 ≤ (10001202373331637/10000000000000000 : ℝ)^4529 := by
      have hnat : (10005318668113573537 : ℕ)^1024*10000000000000000^4529 ≤ 10001202373331637^4529*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005318668113573537 10000000000000000000 10001202373331637 10000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001202373331637/10000000000000000 : ℝ)) (X := (10005318668113573537/10000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5475783778886693/100000000000000000000 : ℝ) ≤ ((15566924156029818023/15570000000000000000 : ℝ)+2*(159128425019/155700000000000 : ℝ)*(2719/25000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (15566924156029818023/15570000000000000000 : ℝ)+2*(159128425019/155700000000000 : ℝ)*(2719/25000 : ℝ)=(10000247602781523/10000000000000000 : ℝ) by norm_num, show 1+2*(5475783778886693/100000000000000000000 : ℝ)=(50005475783778886693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5318668113573537/20000000000000000000 : ℝ)+(5475783778886693/100000000000000000000 : ℝ) ≤ ((15566924156029818023/15570000000000000000 : ℝ)+(159128425019/155700000000000 : ℝ)*((15547/100000 : ℝ)+(2719/25000 : ℝ)))^(4529/1024 : ℝ) := by
    rw [show (15566924156029818023/15570000000000000000 : ℝ)+(159128425019/155700000000000 : ℝ)*((15547/100000 : ℝ)+(2719/25000 : ℝ))=(500036249402829/500000000000000 : ℝ) by norm_num, show 1+(5318668113573537/20000000000000000000 : ℝ)+(5475783778886693/100000000000000000000 : ℝ)=(50016034562173377189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5318668113573537/20000000000000000000 : ℝ) ≤ ((15566924156029818023/15570000000000000000 : ℝ)+2*(159128425019/155700000000000 : ℝ)*(15547/100000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (15566924156029818023/15570000000000000000 : ℝ)+2*(159128425019/155700000000000 : ℝ)*(15547/100000 : ℝ)=(10001202373331637/10000000000000000 : ℝ) by norm_num, show 1+2*(5318668113573537/20000000000000000000 : ℝ)=(10005318668113573537/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15566924156029818023/15570000000000000000 : ℝ)*(X 1 0+X 2 0)+(159128425019/155700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15547/100000 : ℝ)) (c := (15566924156029818023/15570000000000000000 : ℝ)) (alpha := (159128425019/155700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15566924156029818023/15570000000000000000 : ℝ)*(X 0 1+X 2 1)+(159128425019/155700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15547/100000 : ℝ)) (c := (15566924156029818023/15570000000000000000 : ℝ)) (alpha := (159128425019/155700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15566924156029818023/15570000000000000000 : ℝ)*(X 0 2+X 1 2)+(159128425019/155700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (2719/25000 : ℝ)) (hi := (15547/100000 : ℝ)) (c := (15566924156029818023/15570000000000000000 : ℝ)) (alpha := (159128425019/155700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1860599957/10000000000 : ℝ)*X 0 0+(5432950567/10000000000 : ℝ)*X 0 1+(2608777689/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535140733/1000000000 : ℝ)*X 1 0+(-985456183/5000000000 : ℝ)*X 1 1+(5217555627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351407521/10000000000 : ℝ)*X 2 0+(5217555463/10000000000 : ℝ)*X 2 1+(-1970912329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((853482951/2000000000 : ℝ)*X 0 0+(4028290909/10000000000 : ℝ)*X 0 1+(2259219493/5000000000 : ℝ)*X 0 2+(853482951/2000000000 : ℝ)*X 1 0+(4028290909/10000000000 : ℝ)*X 1 1+(2259219493/5000000000 : ℝ)*X 1 2+(853482951/2000000000 : ℝ)*X 2 0+(4028290909/10000000000 : ℝ)*X 2 1+(2259219493/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-37212571/200000000 : ℝ)*X 0 0+(5218669189/10000000000 : ℝ)*X 0 1+(1086365771/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294821049/10000000000 : ℝ)*X 1 0+(-1756638729/10000000000 : ℝ)*X 1 1+(5431829129/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294820973/10000000000 : ℝ)*X 2 0+(5431829253/10000000000 : ℝ)*X 2 1+(-1756638661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133740381/5000000000 : ℝ)*X 0 0+(4515905513/10000000000 : ℝ)*X 0 1+(251927699/625000000 : ℝ)*X 0 2+(2133740381/5000000000 : ℝ)*X 1 0+(4515905513/10000000000 : ℝ)*X 1 1+(251927699/625000000 : ℝ)*X 1 2+(2133740381/5000000000 : ℝ)*X 2 0+(4515905513/10000000000 : ℝ)*X 2 1+(251927699/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2174013524477831452021874237/259500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (905198609/100000000000000 : ℝ)*(base19) + (1040227499/100000000000000 : ℝ)*(base23) + (3213869/2000000000000 : ℝ)*(upper3) + (820769/5000000000000 : ℝ)*(upper4) + (25234533/12500000000000 : ℝ)*(upper5) + (3341438416566619/100000000000000 : ℝ)*(major0) + (3341438416566619/100000000000000 : ℝ)*(major1) + (167071920828331/5000000000000 : ℝ)*(major2) + (2321322345168709/50000000000000 : ℝ)*(sp0) + (2321330942104119/50000000000000 : ℝ)*(sp1) + (4642661749179349/100000000000000 : ℝ)*(sp2) + (408041342038563/20000000000000 : ℝ)*(sp3) + (18099069429/100000000000000 : ℝ)*(sp4) + (3527138427/50000000000000 : ℝ)*(sp7) + (204021376446967/10000000000000 : ℝ)*(f.failure) + (4642662789406847/100000000000000 : ℝ)*(f.sum) + (35780227855417/5190000000000000000000000000 : ℝ)*base65 + (2650730819254541921/519000000000000000000000000000000 : ℝ)*base68 + (182682273971545129/25950000000000000000000000000000 : ℝ)*base70 + (1532202313054458079/519000000000000000000000000000000 : ℝ)*base71 + (3135766103663/5190000000000000000000000000 : ℝ)*base74 + (35153770297804871/25950000000000000000000000000000 : ℝ)*base75 + (7465658096311525763/1557000000000000000000000000000000 : ℝ)*base78 + (15602379136765525763/1557000000000000000000000000000000 : ℝ)*base80 + (3122928300667/973125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10331313/1000000000000000000000 : ℝ)*base89 + (10331313/1000000000000000000000 : ℝ)*base91 + (331313/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (960647457382124411507/129750000000000000000000000 : ℝ) := by norm_num
    linear_combination (33885463/25000000000000 : ℝ)*(base19) + (96793299/20000000000000 : ℝ)*(base23) + (95854629/100000000000000 : ℝ)*(upper3) + (170911811/100000000000000 : ℝ)*(lower4) + (337645320963269/10000000000000 : ℝ)*(major0) + (337645320963269/10000000000000 : ℝ)*(major1) + (3376453209632691/100000000000000 : ℝ)*(major2) + (2207580073/50000000000000 : ℝ)*(sp1) + (13114517719/100000000000000 : ℝ)*(sp2) + (285775383/25000000000000 : ℝ)*(sp3) + (1172828273376559/25000000000000 : ℝ)*(sp4) + (4691308542804239/100000000000000 : ℝ)*(sp5) + (2345649747511011/50000000000000 : ℝ)*(sp6) + (1030795967931569/50000000000000 : ℝ)*(sp7) + (206159307896467/10000000000000 : ℝ)*(f.failure) + (1172828273376559/25000000000000 : ℝ)*(f.sum) + (46395023541881/15570000000000000000000000000 : ℝ)*base66 + (687891252778287187/155700000000000000000000000000000 : ℝ)*base67 + (8780323378244789893/1557000000000000000000000000000000 : ℝ)*base69 + (738046360381412813/155700000000000000000000000000000 : ℝ)*base72 + (23397552854689/15570000000000000000000000000 : ℝ)*base73 + (17355602548056210107/1557000000000000000000000000000000 : ℝ)*base76 + (1729101041881402813/155700000000000000000000000000000 : ℝ)*base78 + (1221130113281797187/155700000000000000000000000000000 : ℝ)*base79 + (574969061957/311400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2538187/1000000000000000000000 : ℝ)*base90 + (2538187/1000000000000000000000 : ℝ)*base92 + (12538187/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1517_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15547/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2719/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1517_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1517_s5_0 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-930325433/5000000000 : ℝ)*x 0 + (1086524261/2000000000 : ℝ)*x 1 + (652231359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930325433/5000000000 : ℝ)^4531 ≤ (11387180378843/100000000000000 : ℝ)^3507 := by
    have hnat : (930325433 : ℕ)^4531*100000000000000^3507 ≤ 11387180378843^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930325433 5000000000 11387180378843 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086524261/2000000000 : ℝ)^4531 ≤ (45460636432959/100000000000000 : ℝ)^3507 := by
    have hnat : (1086524261 : ℕ)^4531*100000000000000^3507 ≤ 45460636432959^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086524261 2000000000 45460636432959 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652231359/1250000000 : ℝ)^4531 ≤ (43152183171099/100000000000000 : ℝ)^3507 := by
    have hnat : (652231359 : ℕ)^4531*100000000000000^3507 ≤ 43152183171099^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652231359 1250000000 43152183171099 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-930325433/5000000000 : ℝ), (1086524261/2000000000 : ℝ), (652231359/1250000000 : ℝ)] ![(11387180378843/100000000000000 : ℝ), (45460636432959/100000000000000 : ℝ), (43152183171099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-930325433/5000000000 : ℝ)|^4531 ≤ (11387180378843/100000000000000 : ℝ)^3507
        have hw : |(-930325433/5000000000 : ℝ)|=(930325433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086524261/2000000000 : ℝ)|^4531 ≤ (45460636432959/100000000000000 : ℝ)^3507
        have hw : |(1086524261/2000000000 : ℝ)|=(1086524261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652231359/1250000000 : ℝ)|^4531 ≤ (43152183171099/100000000000000 : ℝ)^3507
        have hw : |(652231359/1250000000 : ℝ)|=(652231359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_1 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351320947/10000000000 : ℝ)*x 0 + (-78825427/400000000 : ℝ)*x 1 + (41742807/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351320947/10000000000 : ℝ)^4531 ≤ (43538660197/97656250000 : ℝ)^3507 := by
    have hnat : (5351320947 : ℕ)^4531*97656250000^3507 ≤ 43538660197^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351320947 10000000000 43538660197 97656250000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78825427/400000000 : ℝ)^4531 ≤ (2452845749857/20000000000000 : ℝ)^3507 := by
    have hnat : (78825427 : ℕ)^4531*20000000000000^3507 ≤ 2452845749857^3507*400000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78825427 400000000 2452845749857 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41742807/80000000 : ℝ)^4531 ≤ (21576091601577/50000000000000 : ℝ)^3507 := by
    have hnat : (41742807 : ℕ)^4531*50000000000000^3507 ≤ 21576091601577^3507*80000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41742807 80000000 21576091601577 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351320947/10000000000 : ℝ), (-78825427/400000000 : ℝ), (41742807/80000000 : ℝ)] ![(43538660197/97656250000 : ℝ), (2452845749857/20000000000000 : ℝ), (21576091601577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351320947/10000000000 : ℝ)|^4531 ≤ (43538660197/97656250000 : ℝ)^3507
        have hw : |(5351320947/10000000000 : ℝ)|=(5351320947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78825427/400000000 : ℝ)|^4531 ≤ (2452845749857/20000000000000 : ℝ)^3507
        have hw : |(-78825427/400000000 : ℝ)|=(78825427/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41742807/80000000 : ℝ)|^4531 ≤ (21576091601577/50000000000000 : ℝ)^3507
        have hw : |(41742807/80000000 : ℝ)|=(41742807/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_2 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337830237/2500000000 : ℝ)*x 0 + (5217850873/10000000000 : ℝ)*x 1 + (-78825427/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337830237/2500000000 : ℝ)^4531 ≤ (11145897013123/25000000000000 : ℝ)^3507 := by
    have hnat : (1337830237 : ℕ)^4531*25000000000000^3507 ≤ 11145897013123^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337830237 2500000000 11145897013123 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217850873/10000000000 : ℝ)^4531 ≤ (5394022897723/12500000000000 : ℝ)^3507 := by
    have hnat : (5217850873 : ℕ)^4531*12500000000000^3507 ≤ 5394022897723^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217850873 10000000000 5394022897723 12500000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78825427/400000000 : ℝ)^4531 ≤ (2452845749857/20000000000000 : ℝ)^3507 := by
    have hnat : (78825427 : ℕ)^4531*20000000000000^3507 ≤ 2452845749857^3507*400000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78825427 400000000 2452845749857 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337830237/2500000000 : ℝ), (5217850873/10000000000 : ℝ), (-78825427/400000000 : ℝ)] ![(11145897013123/25000000000000 : ℝ), (5394022897723/12500000000000 : ℝ), (2452845749857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337830237/2500000000 : ℝ)|^4531 ≤ (11145897013123/25000000000000 : ℝ)^3507
        have hw : |(1337830237/2500000000 : ℝ)|=(1337830237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217850873/10000000000 : ℝ)|^4531 ≤ (5394022897723/12500000000000 : ℝ)^3507
        have hw : |(5217850873/10000000000 : ℝ)|=(5217850873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78825427/400000000 : ℝ)|^4531 ≤ (2452845749857/20000000000000 : ℝ)^3507
        have hw : |(-78825427/400000000 : ℝ)|=(78825427/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_3 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066861441/2500000000 : ℝ)*x 0 + (2014499019/5000000000 : ℝ)*x 1 + (2258862321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066861441/2500000000 : ℝ)^4531 ≤ (6655975350989/20000000000000 : ℝ)^3507 := by
    have hnat : (1066861441 : ℕ)^4531*20000000000000^3507 ≤ 6655975350989^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066861441 2500000000 6655975350989 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014499019/5000000000 : ℝ)^4531 ≤ (15448615134241/50000000000000 : ℝ)^3507 := by
    have hnat : (2014499019 : ℕ)^4531*50000000000000^3507 ≤ 15448615134241^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014499019 5000000000 15448615134241 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258862321/5000000000 : ℝ)^4531 ≤ (8955723240199/25000000000000 : ℝ)^3507 := by
    have hnat : (2258862321 : ℕ)^4531*25000000000000^3507 ≤ 8955723240199^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258862321 5000000000 8955723240199 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066861441/2500000000 : ℝ), (2014499019/5000000000 : ℝ), (2258862321/5000000000 : ℝ)] ![(6655975350989/20000000000000 : ℝ), (15448615134241/50000000000000 : ℝ), (8955723240199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066861441/2500000000 : ℝ)|^4531 ≤ (6655975350989/20000000000000 : ℝ)^3507
        have hw : |(1066861441/2500000000 : ℝ)|=(1066861441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014499019/5000000000 : ℝ)|^4531 ≤ (15448615134241/50000000000000 : ℝ)^3507
        have hw : |(2014499019/5000000000 : ℝ)|=(2014499019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258862321/5000000000 : ℝ)|^4531 ≤ (8955723240199/25000000000000 : ℝ)^3507
        have hw : |(2258862321/5000000000 : ℝ)|=(2258862321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_4 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372135931/2000000000 : ℝ)*x 0 + (1304739463/2500000000 : ℝ)*x 1 + (1357876541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372135931/2000000000 : ℝ)^4531 ≤ (5693704006431/50000000000000 : ℝ)^3507 := by
    have hnat : (372135931 : ℕ)^4531*50000000000000^3507 ≤ 5693704006431^3507*2000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372135931 2000000000 5693704006431 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304739463/2500000000 : ℝ)^4531 ≤ (10791002869819/25000000000000 : ℝ)^3507 := by
    have hnat : (1304739463 : ℕ)^4531*25000000000000^3507 ≤ 10791002869819^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304739463 2500000000 10791002869819 25000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357876541/2500000000 : ℝ)^4531 ≤ (22724290245573/50000000000000 : ℝ)^3507 := by
    have hnat : (1357876541 : ℕ)^4531*50000000000000^3507 ≤ 22724290245573^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357876541 2500000000 22724290245573 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372135931/2000000000 : ℝ), (1304739463/2500000000 : ℝ), (1357876541/2500000000 : ℝ)] ![(5693704006431/50000000000000 : ℝ), (10791002869819/25000000000000 : ℝ), (22724290245573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372135931/2000000000 : ℝ)|^4531 ≤ (5693704006431/50000000000000 : ℝ)^3507
        have hw : |(-372135931/2000000000 : ℝ)|=(372135931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304739463/2500000000 : ℝ)|^4531 ≤ (10791002869819/25000000000000 : ℝ)^3507
        have hw : |(1304739463/2500000000 : ℝ)|=(1304739463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357876541/2500000000 : ℝ)|^4531 ≤ (22724290245573/50000000000000 : ℝ)^3507
        have hw : |(1357876541/2500000000 : ℝ)|=(1357876541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_5 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330931179/625000000 : ℝ)*x 0 + (-878490193/5000000000 : ℝ)*x 1 + (1357876541/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330931179/625000000 : ℝ)^4531 ≤ (21988599926449/50000000000000 : ℝ)^3507 := by
    have hnat : (330931179 : ℕ)^4531*50000000000000^3507 ≤ 21988599926449^3507*625000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330931179 625000000 21988599926449 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878490193/5000000000 : ℝ)^4531 ≤ (132177745611/1250000000000 : ℝ)^3507 := by
    have hnat : (878490193 : ℕ)^4531*1250000000000^3507 ≤ 132177745611^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878490193 5000000000 132177745611 1250000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357876541/2500000000 : ℝ)^4531 ≤ (22724290245573/50000000000000 : ℝ)^3507 := by
    have hnat : (1357876541 : ℕ)^4531*50000000000000^3507 ≤ 22724290245573^3507*2500000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357876541 2500000000 22724290245573 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330931179/625000000 : ℝ), (-878490193/5000000000 : ℝ), (1357876541/2500000000 : ℝ)] ![(21988599926449/50000000000000 : ℝ), (132177745611/1250000000000 : ℝ), (22724290245573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330931179/625000000 : ℝ)|^4531 ≤ (21988599926449/50000000000000 : ℝ)^3507
        have hw : |(330931179/625000000 : ℝ)|=(330931179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878490193/5000000000 : ℝ)|^4531 ≤ (132177745611/1250000000000 : ℝ)^3507
        have hw : |(-878490193/5000000000 : ℝ)|=(878490193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357876541/2500000000 : ℝ)|^4531 ≤ (22724290245573/50000000000000 : ℝ)^3507
        have hw : |(1357876541/2500000000 : ℝ)|=(1357876541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_6 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330931179/625000000 : ℝ)*x 0 + (5431506163/10000000000 : ℝ)*x 1 + (-878490193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330931179/625000000 : ℝ)^4531 ≤ (21988599926449/50000000000000 : ℝ)^3507 := by
    have hnat : (330931179 : ℕ)^4531*50000000000000^3507 ≤ 21988599926449^3507*625000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330931179 625000000 21988599926449 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431506163/10000000000 : ℝ)^4531 ≤ (9089716096067/20000000000000 : ℝ)^3507 := by
    have hnat : (5431506163 : ℕ)^4531*20000000000000^3507 ≤ 9089716096067^3507*10000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431506163 10000000000 9089716096067 20000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878490193/5000000000 : ℝ)^4531 ≤ (132177745611/1250000000000 : ℝ)^3507 := by
    have hnat : (878490193 : ℕ)^4531*1250000000000^3507 ≤ 132177745611^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878490193 5000000000 132177745611 1250000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330931179/625000000 : ℝ), (5431506163/10000000000 : ℝ), (-878490193/5000000000 : ℝ)] ![(21988599926449/50000000000000 : ℝ), (9089716096067/20000000000000 : ℝ), (132177745611/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330931179/625000000 : ℝ)|^4531 ≤ (21988599926449/50000000000000 : ℝ)^3507
        have hw : |(330931179/625000000 : ℝ)|=(330931179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431506163/10000000000 : ℝ)|^4531 ≤ (9089716096067/20000000000000 : ℝ)^3507
        have hw : |(5431506163/10000000000 : ℝ)|=(5431506163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-878490193/5000000000 : ℝ)|^4531 ≤ (132177745611/1250000000000 : ℝ)^3507
        have hw : |(-878490193/5000000000 : ℝ)|=(878490193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1517_s5_7 (p : ℝ) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133755637/5000000000 : ℝ)*x 0 + (2257602813/5000000000 : ℝ)*x 1 + (503941953/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133755637/5000000000 : ℝ)^4531 ≤ (16640268405309/50000000000000 : ℝ)^3507 := by
    have hnat : (2133755637 : ℕ)^4531*50000000000000^3507 ≤ 16640268405309^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133755637 5000000000 16640268405309 50000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257602813/5000000000 : ℝ)^4531 ≤ (35797088501613/100000000000000 : ℝ)^3507 := by
    have hnat : (2257602813 : ℕ)^4531*100000000000000^3507 ≤ 35797088501613^3507*5000000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257602813 5000000000 35797088501613 100000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503941953/1250000000 : ℝ)^4531 ≤ (1236894987223/4000000000000 : ℝ)^3507 := by
    have hnat : (503941953 : ℕ)^4531*4000000000000^3507 ≤ 1236894987223^3507*1250000000^4531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503941953 1250000000 1236894987223 4000000000000 4531 3507 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4531/1024 : ℝ)) 4531 3507 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133755637/5000000000 : ℝ), (2257602813/5000000000 : ℝ), (503941953/1250000000 : ℝ)] ![(16640268405309/50000000000000 : ℝ), (35797088501613/100000000000000 : ℝ), (1236894987223/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133755637/5000000000 : ℝ)|^4531 ≤ (16640268405309/50000000000000 : ℝ)^3507
        have hw : |(2133755637/5000000000 : ℝ)|=(2133755637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257602813/5000000000 : ℝ)|^4531 ≤ (35797088501613/100000000000000 : ℝ)^3507
        have hw : |(2257602813/5000000000 : ℝ)|=(2257602813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503941953/1250000000 : ℝ)|^4531 ≤ (1236894987223/4000000000000 : ℝ)^3507
        have hw : |(503941953/1250000000 : ℝ)|=(503941953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1517_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5467/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (683/6250 : ℝ) ^ (4529/1024 : ℝ) ≤ (174766502068287/3125000000000000000 : ℝ) := by
    have hpowers : (683/6250 : ℝ)^4529 ≤ (174766502068287/3125000000000000000 : ℝ)^1024 := by
      have hnat : (683 : ℕ)^4529*3125000000000000000^1024 ≤ 174766502068287^1024*6250^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 6250 174766502068287 3125000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/6250 : ℝ)) (X := (174766502068287/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4529/1024 : ℝ) ≤ (6541203435392431/25000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4529 ≤ (6541203435392431/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4529*25000000000000000000^1024 ≤ 6541203435392431^1024*10000^4529 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 6541203435392431 25000000000000000000 4529 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (6541203435392431/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562674766502068287/1562500000000000000 : ℝ) ≤ (5000126440735233/5000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (1562674766502068287/1562500000000000000 : ℝ)^1024 ≤ (5000126440735233/5000000000000000 : ℝ)^4529 := by
      have hnat : (1562674766502068287 : ℕ)^1024*5000000000000000^4529 ≤ 5000126440735233^4529*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562674766502068287 1562500000000000000 5000126440735233 5000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000126440735233/5000000000000000 : ℝ)) (X := (1562674766502068287/1562500000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007939335451938727/25000000000000000000 : ℝ) ≤ (1000071794044141/1000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (25007939335451938727/25000000000000000000 : ℝ)^1024 ≤ (1000071794044141/1000000000000000 : ℝ)^4529 := by
      have hnat : (25007939335451938727 : ℕ)^1024*1000000000000000^4529 ≤ 1000071794044141^4529*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007939335451938727 25000000000000000000 1000071794044141 1000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000071794044141/1000000000000000 : ℝ)) (X := (25007939335451938727/25000000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506541203435392431/12500000000000000000 : ℝ) ≤ (5000591499706177/5000000000000000 : ℝ) ^ (4529/1024 : ℝ) := by
    have hpowers : (12506541203435392431/12500000000000000000 : ℝ)^1024 ≤ (5000591499706177/5000000000000000 : ℝ)^4529 := by
      have hnat : (12506541203435392431 : ℕ)^1024*5000000000000000^4529 ≤ 5000591499706177^4529*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506541203435392431 12500000000000000000 5000591499706177 5000000000000000 1024 4529 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000591499706177/5000000000000000 : ℝ)) (X := (12506541203435392431/12500000000000000000 : ℝ)) (by norm_num) 4529 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(174766502068287/3125000000000000000 : ℝ) ≤ ((11402747329099828457/11405000000000000000 : ℝ)+2*(7266546421/7128125000000 : ℝ)*(683/6250 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (11402747329099828457/11405000000000000000 : ℝ)+2*(7266546421/7128125000000 : ℝ)*(683/6250 : ℝ)=(5000126440735233/5000000000000000 : ℝ) by norm_num, show 1+2*(174766502068287/3125000000000000000 : ℝ)=(1562674766502068287/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6541203435392431/25000000000000000000 : ℝ)+(174766502068287/3125000000000000000 : ℝ) ≤ ((11402747329099828457/11405000000000000000 : ℝ)+(7266546421/7128125000000 : ℝ)*((1549/10000 : ℝ)+(683/6250 : ℝ)))^(4529/1024 : ℝ) := by
    rw [show (11402747329099828457/11405000000000000000 : ℝ)+(7266546421/7128125000000 : ℝ)*((1549/10000 : ℝ)+(683/6250 : ℝ))=(1000071794044141/1000000000000000 : ℝ) by norm_num, show 1+(6541203435392431/25000000000000000000 : ℝ)+(174766502068287/3125000000000000000 : ℝ)=(25007939335451938727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6541203435392431/25000000000000000000 : ℝ) ≤ ((11402747329099828457/11405000000000000000 : ℝ)+2*(7266546421/7128125000000 : ℝ)*(1549/10000 : ℝ))^(4529/1024 : ℝ) := by
    rw [show (11402747329099828457/11405000000000000000 : ℝ)+2*(7266546421/7128125000000 : ℝ)*(1549/10000 : ℝ)=(5000591499706177/5000000000000000 : ℝ) by norm_num, show 1+2*(6541203435392431/25000000000000000000 : ℝ)=(12506541203435392431/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11402747329099828457/11405000000000000000 : ℝ)*(X 1 0+X 2 0)+(7266546421/7128125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11402747329099828457/11405000000000000000 : ℝ)) (alpha := (7266546421/7128125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11402747329099828457/11405000000000000000 : ℝ)*(X 0 1+X 2 1)+(7266546421/7128125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11402747329099828457/11405000000000000000 : ℝ)) (alpha := (7266546421/7128125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11402747329099828457/11405000000000000000 : ℝ)*(X 0 2+X 1 2)+(7266546421/7128125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4529/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11402747329099828457/11405000000000000000 : ℝ)) (alpha := (7266546421/7128125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-930325433/5000000000 : ℝ)*X 0 0+(1086524261/2000000000 : ℝ)*X 0 1+(652231359/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351320947/10000000000 : ℝ)*X 1 0+(-78825427/400000000 : ℝ)*X 1 1+(41742807/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337830237/2500000000 : ℝ)*X 2 0+(5217850873/10000000000 : ℝ)*X 2 1+(-78825427/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1066861441/2500000000 : ℝ)*X 0 0+(2014499019/5000000000 : ℝ)*X 0 1+(2258862321/5000000000 : ℝ)*X 0 2+(1066861441/2500000000 : ℝ)*X 1 0+(2014499019/5000000000 : ℝ)*X 1 1+(2258862321/5000000000 : ℝ)*X 1 2+(1066861441/2500000000 : ℝ)*X 2 0+(2014499019/5000000000 : ℝ)*X 2 1+(2258862321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372135931/2000000000 : ℝ)*X 0 0+(1304739463/2500000000 : ℝ)*X 0 1+(1357876541/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330931179/625000000 : ℝ)*X 1 0+(-878490193/5000000000 : ℝ)*X 1 1+(1357876541/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330931179/625000000 : ℝ)*X 2 0+(5431506163/10000000000 : ℝ)*X 2 1+(-878490193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2133755637/5000000000 : ℝ)*X 0 0+(2257602813/5000000000 : ℝ)*X 0 1+(503941953/1250000000 : ℝ)*X 0 2+(2133755637/5000000000 : ℝ)*X 1 0+(2257602813/5000000000 : ℝ)*X 1 1+(503941953/1250000000 : ℝ)*X 1 2+(2133755637/5000000000 : ℝ)*X 2 0+(2257602813/5000000000 : ℝ)*X 2 1+(503941953/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1517_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1533092636834217291267637269/142562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1878874723/100000000000000 : ℝ)*(base19) + (1753593381/100000000000000 : ℝ)*(base23) + (67507687/100000000000000 : ℝ)*(lower2) + (133925259/50000000000000 : ℝ)*(upper3) + (175371767/100000000000000 : ℝ)*(upper5) + (1675588870379339/50000000000000 : ℝ)*(major0) + (1675588870379339/50000000000000 : ℝ)*(major1) + (1675588870379339/50000000000000 : ℝ)*(major2) + (2328082572092251/50000000000000 : ℝ)*(sp0) + (2328096424056627/50000000000000 : ℝ)*(sp1) + (931238594678919/20000000000000 : ℝ)*(sp2) + (2046146307667293/100000000000000 : ℝ)*(sp3) + (1183312139/4000000000000 : ℝ)*(sp4) + (7044200569/50000000000000 : ℝ)*(sp7) + (2046160396068431/100000000000000 : ℝ)*(f.failure) + (4656194726987977/100000000000000 : ℝ)*(f.sum) + (5367056592181/11405000000000000000000000000 : ℝ)*base65 + (7829005503755550077/570250000000000000000000000000000 : ℝ)*base68 + (4142028769738050077/570250000000000000000000000000000 : ℝ)*base70 + (6080752368123050077/570250000000000000000000000000000 : ℝ)*base72 + (3760158805009/712812500000000000000000000 : ℝ)*base74 + (5356827558059550077/570250000000000000000000000000000 : ℝ)*base76 + (1141495518206449923/570250000000000000000000000000000 : ℝ)*base77 + (2613544980161800077/570250000000000000000000000000000 : ℝ)*base80 + (45222681122149/11405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6268391/10000000000000000000000 : ℝ)*base90 + (6268391/10000000000000000000000 : ℝ)*base92 + (6268391/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (578998127140518017469226317/142562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (659081839/100000000000000 : ℝ)*(base19) + (89454383/12500000000000 : ℝ)*(base23) + (108664789/50000000000000 : ℝ)*(lower1) + (83771547/100000000000000 : ℝ)*(upper3) + (25674887/100000000000000 : ℝ)*(lower4) + (83962847/100000000000000 : ℝ)*(upper5) + (1693080735464673/50000000000000 : ℝ)*(major0) + (1693080735464673/50000000000000 : ℝ)*(major1) + (1693080735464673/50000000000000 : ℝ)*(major2) + (11823479/1562500000000 : ℝ)*(sp2) + (940960412456659/20000000000000 : ℝ)*(sp4) + (294050087700091/6250000000000 : ℝ)*(sp5) + (188192023597823/4000000000000 : ℝ)*(sp6) + (516880186049149/25000000000000 : ℝ)*(sp7) + (516880186049149/25000000000000 : ℝ)*(f.failure) + (940960412456659/20000000000000 : ℝ)*(f.sum) + (77887812760317/11405000000000000000000000000 : ℝ)*base65 + (14332597765637399561/570250000000000000000000000000000 : ℝ)*base67 + (4663475918565399561/570250000000000000000000000000000 : ℝ)*base69 + (5560192330534399561/570250000000000000000000000000000 : ℝ)*base71 + (1185803535761/1425625000000000000000000000 : ℝ)*base74 + (34621642152815600439/570250000000000000000000000000000 : ℝ)*base76 + (3272452714578399561/570250000000000000000000000000000 : ℝ)*base77 + (5682238820259149561/570250000000000000000000000000000 : ℝ)*base79 + (33123757674971/5702500000000000000000000000 : ℝ)*base81 + (29841989/2500000000000000000000 : ℝ)*base90 + (29841989/2500000000000000000000 : ℝ)*base92 + (29841989/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1517_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1517_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1517_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7989/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1517_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1517_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1517_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4529/1024 : ℝ) ≤ p) (hpb : p ≤ (4531/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163778839/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7989/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (131/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5467/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1517_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
