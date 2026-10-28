-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1140_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:34.495136+00:00
-- url     : https://prove2.me/submissions/d7c563bf-1367-45b1-9597-7c1e0e006755

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
theorem support_rectangle_w1140_s6_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167812573/10000000000 : ℝ)*x 0 + (5393422291/10000000000 : ℝ)*x 1 + (526537473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167812573/10000000000 : ℝ)^8333 ≤ (2634455988379/20000000000000 : ℝ)^6285 := by
    have hnat : (2167812573 : ℕ)^8333*20000000000000^6285 ≤ 2634455988379^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167812573 10000000000 2634455988379 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393422291/10000000000 : ℝ)^8333 ≤ (5513165943077/12500000000000 : ℝ)^6285 := by
    have hnat : (5393422291 : ℕ)^8333*12500000000000^6285 ≤ 5513165943077^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393422291 10000000000 5513165943077 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526537473/1000000000 : ℝ)^8333 ≤ (42722392501701/100000000000000 : ℝ)^6285 := by
    have hnat : (526537473 : ℕ)^8333*100000000000000^6285 ≤ 42722392501701^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526537473 1000000000 42722392501701 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167812573/10000000000 : ℝ), (5393422291/10000000000 : ℝ), (526537473/1000000000 : ℝ)] ![(2634455988379/20000000000000 : ℝ), (5513165943077/12500000000000 : ℝ), (42722392501701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167812573/10000000000 : ℝ)|^8333 ≤ (2634455988379/20000000000000 : ℝ)^6285
        have hw : |(-2167812573/10000000000 : ℝ)|=(2167812573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393422291/10000000000 : ℝ)|^8333 ≤ (5513165943077/12500000000000 : ℝ)^6285
        have hw : |(5393422291/10000000000 : ℝ)|=(5393422291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526537473/1000000000 : ℝ)|^8333 ≤ (42722392501701/100000000000000 : ℝ)^6285
        have hw : |(526537473/1000000000 : ℝ)|=(526537473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672426619/5000000000 : ℝ)*x 0 + (-2232766551/10000000000 : ℝ)*x 1 + (1053074977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672426619/5000000000 : ℝ)^8333 ≤ (43579499918389/100000000000000 : ℝ)^6285 := by
    have hnat : (2672426619 : ℕ)^8333*100000000000000^6285 ≤ 43579499918389^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672426619 5000000000 43579499918389 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2232766551/10000000000 : ℝ)^8333 ≤ (6849052947959/50000000000000 : ℝ)^6285 := by
    have hnat : (2232766551 : ℕ)^8333*50000000000000^6285 ≤ 6849052947959^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232766551 10000000000 6849052947959 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053074977/2000000000 : ℝ)^8333 ≤ (10680598542289/25000000000000 : ℝ)^6285 := by
    have hnat : (1053074977 : ℕ)^8333*25000000000000^6285 ≤ 10680598542289^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053074977 2000000000 10680598542289 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672426619/5000000000 : ℝ), (-2232766551/10000000000 : ℝ), (1053074977/2000000000 : ℝ)] ![(43579499918389/100000000000000 : ℝ), (6849052947959/50000000000000 : ℝ), (10680598542289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672426619/5000000000 : ℝ)|^8333 ≤ (43579499918389/100000000000000 : ℝ)^6285
        have hw : |(2672426619/5000000000 : ℝ)|=(2672426619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2232766551/10000000000 : ℝ)|^8333 ≤ (6849052947959/50000000000000 : ℝ)^6285
        have hw : |(-2232766551/10000000000 : ℝ)|=(2232766551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053074977/2000000000 : ℝ)|^8333 ≤ (10680598542289/25000000000000 : ℝ)^6285
        have hw : |(1053074977/2000000000 : ℝ)|=(1053074977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336213477/2500000000 : ℝ)*x 0 + (5265374177/10000000000 : ℝ)*x 1 + (-2232766597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336213477/2500000000 : ℝ)^8333 ≤ (43579507161371/100000000000000 : ℝ)^6285 := by
    have hnat : (1336213477 : ℕ)^8333*100000000000000^6285 ≤ 43579507161371^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336213477 2500000000 43579507161371 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265374177/10000000000 : ℝ)^8333 ≤ (10680596638163/25000000000000 : ℝ)^6285 := by
    have hnat : (5265374177 : ℕ)^8333*25000000000000^6285 ≤ 10680596638163^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265374177 10000000000 10680596638163 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2232766597/10000000000 : ℝ)^8333 ≤ (1369810627009/10000000000000 : ℝ)^6285 := by
    have hnat : (2232766597 : ℕ)^8333*10000000000000^6285 ≤ 1369810627009^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232766597 10000000000 1369810627009 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336213477/2500000000 : ℝ), (5265374177/10000000000 : ℝ), (-2232766597/10000000000 : ℝ)] ![(43579507161371/100000000000000 : ℝ), (10680596638163/25000000000000 : ℝ), (1369810627009/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336213477/2500000000 : ℝ)|^8333 ≤ (43579507161371/100000000000000 : ℝ)^6285
        have hw : |(1336213477/2500000000 : ℝ)|=(1336213477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265374177/10000000000 : ℝ)|^8333 ≤ (10680596638163/25000000000000 : ℝ)^6285
        have hw : |(5265374177/10000000000 : ℝ)|=(5265374177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2232766597/10000000000 : ℝ)|^8333 ≤ (1369810627009/10000000000000 : ℝ)^6285
        have hw : |(-2232766597/10000000000 : ℝ)|=(2232766597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182469013/5000000000 : ℝ)*x 0 + (2119730661/5000000000 : ℝ)*x 1 + (561763827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182469013/5000000000 : ℝ)^8333 ≤ (33316783285037/100000000000000 : ℝ)^6285 := by
    have hnat : (2182469013 : ℕ)^8333*100000000000000^6285 ≤ 33316783285037^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182469013 5000000000 33316783285037 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119730661/5000000000 : ℝ)^8333 ≤ (32052943619273/100000000000000 : ℝ)^6285 := by
    have hnat : (2119730661 : ℕ)^8333*100000000000000^6285 ≤ 32052943619273^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119730661 5000000000 32052943619273 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561763827/1250000000 : ℝ)^8333 ≤ (34630273076981/100000000000000 : ℝ)^6285 := by
    have hnat : (561763827 : ℕ)^8333*100000000000000^6285 ≤ 34630273076981^6285*1250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561763827 1250000000 34630273076981 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182469013/5000000000 : ℝ), (2119730661/5000000000 : ℝ), (561763827/1250000000 : ℝ)] ![(33316783285037/100000000000000 : ℝ), (32052943619273/100000000000000 : ℝ), (34630273076981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182469013/5000000000 : ℝ)|^8333 ≤ (33316783285037/100000000000000 : ℝ)^6285
        have hw : |(2182469013/5000000000 : ℝ)|=(2182469013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2119730661/5000000000 : ℝ)|^8333 ≤ (32052943619273/100000000000000 : ℝ)^6285
        have hw : |(2119730661/5000000000 : ℝ)|=(2119730661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561763827/1250000000 : ℝ)|^8333 ≤ (34630273076981/100000000000000 : ℝ)^6285
        have hw : |(561763827/1250000000 : ℝ)|=(561763827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16936077/78125000 : ℝ)*x 0 + (2632848869/5000000000 : ℝ)*x 1 + (539309787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16936077/78125000 : ℝ)^8333 ≤ (2634464500663/20000000000000 : ℝ)^6285 := by
    have hnat : (16936077 : ℕ)^8333*20000000000000^6285 ≤ 2634464500663^6285*78125000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16936077 78125000 2634464500663 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632848869/5000000000 : ℝ)^8333 ≤ (4272586738321/10000000000000 : ℝ)^6285 := by
    have hnat : (2632848869 : ℕ)^8333*10000000000000^6285 ≤ 4272586738321^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632848869 5000000000 4272586738321 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539309787/1000000000 : ℝ)^8333 ≤ (44101810098703/100000000000000 : ℝ)^6285 := by
    have hnat : (539309787 : ℕ)^8333*100000000000000^6285 ≤ 44101810098703^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539309787 1000000000 44101810098703 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16936077/78125000 : ℝ), (2632848869/5000000000 : ℝ), (539309787/1000000000 : ℝ)] ![(2634464500663/20000000000000 : ℝ), (4272586738321/10000000000000 : ℝ), (44101810098703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16936077/78125000 : ℝ)|^8333 ≤ (2634464500663/20000000000000 : ℝ)^6285
        have hw : |(-16936077/78125000 : ℝ)|=(16936077/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632848869/5000000000 : ℝ)|^8333 ≤ (4272586738321/10000000000000 : ℝ)^6285
        have hw : |(2632848869/5000000000 : ℝ)|=(2632848869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539309787/1000000000 : ℝ)|^8333 ≤ (44101810098703/100000000000000 : ℝ)^6285
        have hw : |(539309787/1000000000 : ℝ)|=(539309787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166013033/312500000 : ℝ)*x 0 + (-13156519/62500000 : ℝ)*x 1 + (43144783/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166013033/312500000 : ℝ)^8333 ≤ (10807299588813/25000000000000 : ℝ)^6285 := by
    have hnat : (166013033 : ℕ)^8333*25000000000000^6285 ≤ 10807299588813^6285*312500000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166013033 312500000 10807299588813 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13156519/62500000 : ℝ)^8333 ≤ (1583623934151/12500000000000 : ℝ)^6285 := by
    have hnat : (13156519 : ℕ)^8333*12500000000000^6285 ≤ 1583623934151^6285*62500000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13156519 62500000 1583623934151 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43144783/80000000 : ℝ)^8333 ≤ (22050905076457/50000000000000 : ℝ)^6285 := by
    have hnat : (43144783 : ℕ)^8333*50000000000000^6285 ≤ 22050905076457^6285*80000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43144783 80000000 22050905076457 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166013033/312500000 : ℝ), (-13156519/62500000 : ℝ), (43144783/80000000 : ℝ)] ![(10807299588813/25000000000000 : ℝ), (1583623934151/12500000000000 : ℝ), (22050905076457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166013033/312500000 : ℝ)|^8333 ≤ (10807299588813/25000000000000 : ℝ)^6285
        have hw : |(166013033/312500000 : ℝ)|=(166013033/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13156519/62500000 : ℝ)|^8333 ≤ (1583623934151/12500000000000 : ℝ)^6285
        have hw : |(-13156519/62500000 : ℝ)|=(13156519/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43144783/80000000 : ℝ)|^8333 ≤ (22050905076457/50000000000000 : ℝ)^6285
        have hw : |(43144783/80000000 : ℝ)|=(43144783/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656208529/5000000000 : ℝ)*x 0 + (5393097881/10000000000 : ℝ)*x 1 + (-210504303/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656208529/5000000000 : ℝ)^8333 ≤ (4322919837683/10000000000000 : ℝ)^6285 := by
    have hnat : (2656208529 : ℕ)^8333*10000000000000^6285 ≤ 4322919837683^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656208529 5000000000 4322919837683 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393097881/10000000000 : ℝ)^8333 ≤ (22050905108983/50000000000000 : ℝ)^6285 := by
    have hnat : (5393097881 : ℕ)^8333*50000000000000^6285 ≤ 22050905108983^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393097881 10000000000 22050905108983 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210504303/1000000000 : ℝ)^8333 ≤ (12668991393413/100000000000000 : ℝ)^6285 := by
    have hnat : (210504303 : ℕ)^8333*100000000000000^6285 ≤ 12668991393413^6285*1000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210504303 1000000000 12668991393413 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656208529/5000000000 : ℝ), (5393097881/10000000000 : ℝ), (-210504303/1000000000 : ℝ)] ![(4322919837683/10000000000000 : ℝ), (22050905108983/50000000000000 : ℝ), (12668991393413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656208529/5000000000 : ℝ)|^8333 ≤ (4322919837683/10000000000000 : ℝ)^6285
        have hw : |(2656208529/5000000000 : ℝ)|=(2656208529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393097881/10000000000 : ℝ)|^8333 ≤ (22050905108983/50000000000000 : ℝ)^6285
        have hw : |(5393097881/10000000000 : ℝ)|=(5393097881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210504303/1000000000 : ℝ)|^8333 ≤ (12668991393413/100000000000000 : ℝ)^6285
        have hw : |(-210504303/1000000000 : ℝ)|=(210504303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s6_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182473687/5000000000 : ℝ)*x 0 + (1123366833/2500000000 : ℝ)*x 1 + (4240107483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182473687/5000000000 : ℝ)^8333 ≤ (16658438943477/50000000000000 : ℝ)^6285 := by
    have hnat : (2182473687 : ℕ)^8333*50000000000000^6285 ≤ 16658438943477^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182473687 5000000000 16658438943477 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123366833/2500000000 : ℝ)^8333 ≤ (1384948041067/4000000000000 : ℝ)^6285 := by
    have hnat : (1123366833 : ℕ)^8333*4000000000000^6285 ≤ 1384948041067^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123366833 2500000000 1384948041067 4000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240107483/10000000000 : ℝ)^8333 ≤ (32059421081189/100000000000000 : ℝ)^6285 := by
    have hnat : (4240107483 : ℕ)^8333*100000000000000^6285 ≤ 32059421081189^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240107483 10000000000 32059421081189 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182473687/5000000000 : ℝ), (1123366833/2500000000 : ℝ), (4240107483/10000000000 : ℝ)] ![(16658438943477/50000000000000 : ℝ), (1384948041067/4000000000000 : ℝ), (32059421081189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182473687/5000000000 : ℝ)|^8333 ≤ (16658438943477/50000000000000 : ℝ)^6285
        have hw : |(2182473687/5000000000 : ℝ)|=(2182473687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123366833/2500000000 : ℝ)|^8333 ≤ (1384948041067/4000000000000 : ℝ)^6285
        have hw : |(1123366833/2500000000 : ℝ)|=(1123366833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240107483/10000000000 : ℝ)|^8333 ≤ (32059421081189/100000000000000 : ℝ)^6285
        have hw : |(4240107483/10000000000 : ℝ)|=(4240107483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1757/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (707/6250 : ℝ) ^ (2083/512 : ℝ) ≤ (14107762196355063/100000000000000000000 : ℝ) := by
    have hpowers : (707/6250 : ℝ)^2083 ≤ (14107762196355063/100000000000000000000 : ℝ)^512 := by
      have hnat : (707 : ℕ)^2083*100000000000000000000^512 ≤ 14107762196355063^512*6250^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 6250 14107762196355063 100000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/6250 : ℝ)) (X := (14107762196355063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (2083/512 : ℝ) ≤ (2153244081825237/6250000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^2083 ≤ (2153244081825237/6250000000000000000 : ℝ)^512 := by
      have hnat : (1761 : ℕ)^2083*6250000000000000000^512 ≤ 2153244081825237^512*12500^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 2153244081825237 6250000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (2153244081825237/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014107762196355063/50000000000000000000 : ℝ) ≤ (10000693461912581/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (50014107762196355063/50000000000000000000 : ℝ)^512 ≤ (10000693461912581/10000000000000000 : ℝ)^2083 := by
      have hnat : (50014107762196355063 : ℕ)^512*10000000000000000^2083 ≤ 10000693461912581^2083*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014107762196355063 50000000000000000000 10000693461912581 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000693461912581/10000000000000000 : ℝ)) (X := (50014107762196355063/50000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009711933501111771/20000000000000000000 : ℝ) ≤ (625074585928523/625000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (20009711933501111771/20000000000000000000 : ℝ)^512 ≤ (625074585928523/625000000000000 : ℝ)^2083 := by
      have hnat : (20009711933501111771 : ℕ)^512*625000000000000^2083 ≤ 625074585928523^2083*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009711933501111771 20000000000000000000 625074585928523 625000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074585928523/625000000000000 : ℝ)) (X := (20009711933501111771/20000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127153244081825237/3125000000000000000 : ℝ) ≤ (2000338657560031/2000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (3127153244081825237/3125000000000000000 : ℝ)^512 ≤ (2000338657560031/2000000000000000 : ℝ)^2083 := by
      have hnat : (3127153244081825237 : ℕ)^512*2000000000000000^2083 ≤ 2000338657560031^2083*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127153244081825237 3125000000000000000 2000338657560031 2000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000338657560031/2000000000000000 : ℝ)) (X := (3127153244081825237/3125000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14107762196355063/100000000000000000000 : ℝ) ≤ ((3468826877478635971/3470000000000000000 : ℝ)+2*(499912943787/277600000000000 : ℝ)*(707/6250 : ℝ))^(2083/512 : ℝ) := by
    rw [show (3468826877478635971/3470000000000000000 : ℝ)+2*(499912943787/277600000000000 : ℝ)*(707/6250 : ℝ)=(10000693461912581/10000000000000000 : ℝ) by norm_num, show 1+2*(14107762196355063/100000000000000000000 : ℝ)=(50014107762196355063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2153244081825237/6250000000000000000 : ℝ)+(14107762196355063/100000000000000000000 : ℝ) ≤ ((3468826877478635971/3470000000000000000 : ℝ)+(499912943787/277600000000000 : ℝ)*((1761/12500 : ℝ)+(707/6250 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (3468826877478635971/3470000000000000000 : ℝ)+(499912943787/277600000000000 : ℝ)*((1761/12500 : ℝ)+(707/6250 : ℝ))=(625074585928523/625000000000000 : ℝ) by norm_num, show 1+(2153244081825237/6250000000000000000 : ℝ)+(14107762196355063/100000000000000000000 : ℝ)=(20009711933501111771/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2153244081825237/6250000000000000000 : ℝ) ≤ ((3468826877478635971/3470000000000000000 : ℝ)+2*(499912943787/277600000000000 : ℝ)*(1761/12500 : ℝ))^(2083/512 : ℝ) := by
    rw [show (3468826877478635971/3470000000000000000 : ℝ)+2*(499912943787/277600000000000 : ℝ)*(1761/12500 : ℝ)=(2000338657560031/2000000000000000 : ℝ) by norm_num, show 1+2*(2153244081825237/6250000000000000000 : ℝ)=(3127153244081825237/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3468826877478635971/3470000000000000000 : ℝ)*(X 1 0+X 2 0)+(499912943787/277600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (3468826877478635971/3470000000000000000 : ℝ)) (alpha := (499912943787/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3468826877478635971/3470000000000000000 : ℝ)*(X 0 1+X 2 1)+(499912943787/277600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (3468826877478635971/3470000000000000000 : ℝ)) (alpha := (499912943787/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3468826877478635971/3470000000000000000 : ℝ)*(X 0 2+X 1 2)+(499912943787/277600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (3468826877478635971/3470000000000000000 : ℝ)) (alpha := (499912943787/277600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2167812573/10000000000 : ℝ)*X 0 0+(5393422291/10000000000 : ℝ)*X 0 1+(526537473/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672426619/5000000000 : ℝ)*X 1 0+(-2232766551/10000000000 : ℝ)*X 1 1+(1053074977/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336213477/2500000000 : ℝ)*X 2 0+(5265374177/10000000000 : ℝ)*X 2 1+(-2232766597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182469013/5000000000 : ℝ)*X 0 0+(2119730661/5000000000 : ℝ)*X 0 1+(561763827/1250000000 : ℝ)*X 0 2+(2182469013/5000000000 : ℝ)*X 1 0+(2119730661/5000000000 : ℝ)*X 1 1+(561763827/1250000000 : ℝ)*X 1 2+(2182469013/5000000000 : ℝ)*X 2 0+(2119730661/5000000000 : ℝ)*X 2 1+(561763827/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16936077/78125000 : ℝ)*X 0 0+(2632848869/5000000000 : ℝ)*X 0 1+(539309787/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((166013033/312500000 : ℝ)*X 1 0+(-13156519/62500000 : ℝ)*X 1 1+(43144783/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656208529/5000000000 : ℝ)*X 2 0+(5393097881/10000000000 : ℝ)*X 2 1+(-210504303/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182473687/5000000000 : ℝ)*X 0 0+(1123366833/2500000000 : ℝ)*X 0 1+(4240107483/10000000000 : ℝ)*X 0 2+(2182473687/5000000000 : ℝ)*X 1 0+(1123366833/2500000000 : ℝ)*X 1 1+(4240107483/10000000000 : ℝ)*X 1 2+(2182473687/5000000000 : ℝ)*X 2 0+(1123366833/2500000000 : ℝ)*X 2 1+(4240107483/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1858566208727504675901416901/173500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (563941269/50000000000000 : ℝ)*(base19) + (1413538713/100000000000000 : ℝ)*(base23) + (90592179/20000000000000 : ℝ)*(lower2) + (101237353/25000000000000 : ℝ)*(upper3) + (82394393/100000000000000 : ℝ)*(lower4) + (5868327432724723/100000000000000 : ℝ)*(major0) + (5868327432724723/100000000000000 : ℝ)*(major1) + (5868327432724723/100000000000000 : ℝ)*(major2) + (7809616674563817/100000000000000 : ℝ)*(sp0) + (3904817564442349/50000000000000 : ℝ)*(sp1) + (7809634843228523/100000000000000 : ℝ)*(sp2) + (981746318290881/25000000000000 : ℝ)*(sp3) + (19582203419/100000000000000 : ℝ)*(sp4) + (8244611359/25000000000000 : ℝ)*(sp7) + (6135966018139/156250000000 : ℝ)*(f.failure) + (1952409064191809/25000000000000 : ℝ)*(f.sum) + (34902153129961/13880000000000000000000000000 : ℝ)*base65 + (3063807129990823533/347000000000000000000000000000000 : ℝ)*base67 + (7381727010470176467/347000000000000000000000000000000 : ℝ)*base70 + (584119326029823533/347000000000000000000000000000000 : ℝ)*base71 + (43490389263841/13880000000000000000000000000 : ℝ)*base73 + (1201742993600176467/347000000000000000000000000000000 : ℝ)*base76 + (2992415307309823533/347000000000000000000000000000000 : ℝ)*base77 + (801353388096823533/347000000000000000000000000000000 : ℝ)*base79 + (9462968828921/13880000000000000000000000000 : ℝ)*base81 + (181257/15625000000000000000 : ℝ)*base90 + (181257/15625000000000000000 : ℝ)*base92 + (181257/15625000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (883574981960930379966655641/86750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115708999/6250000000000 : ℝ)*(base19) + (202732643/10000000000000 : ℝ)*(base23) + (102632841/50000000000000 : ℝ)*(upper3) + (76688863/100000000000000 : ℝ)*(lower4) + (207688737/100000000000000 : ℝ)*(upper5) + (5898119274136993/100000000000000 : ℝ)*(major0) + (5898119274136993/100000000000000 : ℝ)*(major1) + (5898119274136993/100000000000000 : ℝ)*(major2) + (10202627029/20000000000000 : ℝ)*(sp1) + (27853757189/50000000000000 : ℝ)*(sp2) + (7849283594312841/100000000000000 : ℝ)*(sp4) + (490576920614607/6250000000000 : ℝ)*(sp5) + (3924612929736017/50000000000000 : ℝ)*(sp6) + (246684663403191/6250000000000 : ℝ)*(sp7) + (246684663403191/6250000000000 : ℝ)*(f.failure) + (7849283594312841/100000000000000 : ℝ)*(f.sum) + (26169074106251/13880000000000000000000000000 : ℝ)*base65 + (2121039444737712703/347000000000000000000000000000000 : ℝ)*base67 + (1199141385658287297/347000000000000000000000000000000 : ℝ)*base70 + (2006247654365712703/347000000000000000000000000000000 : ℝ)*base71 + (22113410439469/13880000000000000000000000000 : ℝ)*base74 + (5056003225056712703/347000000000000000000000000000000 : ℝ)*base75 + (1118759130907712703/347000000000000000000000000000000 : ℝ)*base77 + (3993616893643712703/347000000000000000000000000000000 : ℝ)*base79 + (23854454827931/13880000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4363783/625000000000000000000 : ℝ)*base90 + (4363783/625000000000000000000 : ℝ)*base92 + (4363783/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1140_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1140_s7_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083919753/5000000000 : ℝ)*x 0 + (5393101111/10000000000 : ℝ)*x 1 + (5265678259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083919753/5000000000 : ℝ)^8333 ≤ (3293124230627/25000000000000 : ℝ)^6285 := by
    have hnat : (1083919753 : ℕ)^8333*25000000000000^6285 ≤ 3293124230627^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083919753 5000000000 3293124230627 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393101111/10000000000 : ℝ)^8333 ≤ (22050922619009/50000000000000 : ℝ)^6285 := by
    have hnat : (5393101111 : ℕ)^8333*50000000000000^6285 ≤ 22050922619009^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393101111 10000000000 22050922619009 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265678259/10000000000 : ℝ)^8333 ≤ (8545131565697/20000000000000 : ℝ)^6285 := by
    have hnat : (5265678259 : ℕ)^8333*20000000000000^6285 ≤ 8545131565697^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265678259 10000000000 8545131565697 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083919753/5000000000 : ℝ), (5393101111/10000000000 : ℝ), (5265678259/10000000000 : ℝ)] ![(3293124230627/25000000000000 : ℝ), (22050922619009/50000000000000 : ℝ), (8545131565697/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083919753/5000000000 : ℝ)|^8333 ≤ (3293124230627/25000000000000 : ℝ)^6285
        have hw : |(-1083919753/5000000000 : ℝ)|=(1083919753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393101111/10000000000 : ℝ)|^8333 ≤ (22050922619009/50000000000000 : ℝ)^6285
        have hw : |(5393101111/10000000000 : ℝ)|=(5393101111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265678259/10000000000 : ℝ)|^8333 ≤ (8545131565697/20000000000000 : ℝ)^6285
        have hw : |(5265678259/10000000000 : ℝ)|=(5265678259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672386691/5000000000 : ℝ)*x 0 + (-55811781/250000000 : ℝ)*x 1 + (1053135683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672386691/5000000000 : ℝ)^8333 ≤ (4357863664361/10000000000000 : ℝ)^6285 := by
    have hnat : (2672386691 : ℕ)^8333*10000000000000^6285 ≤ 4357863664361^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672386691 5000000000 4357863664361 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55811781/250000000 : ℝ)^8333 ≤ (13695703837491/100000000000000 : ℝ)^6285 := by
    have hnat : (55811781 : ℕ)^8333*100000000000000^6285 ≤ 13695703837491^6285*250000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55811781 250000000 13695703837491 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053135683/2000000000 : ℝ)^8333 ≤ (42725659506729/100000000000000 : ℝ)^6285 := by
    have hnat : (1053135683 : ℕ)^8333*100000000000000^6285 ≤ 42725659506729^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053135683 2000000000 42725659506729 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672386691/5000000000 : ℝ), (-55811781/250000000 : ℝ), (1053135683/2000000000 : ℝ)] ![(4357863664361/10000000000000 : ℝ), (13695703837491/100000000000000 : ℝ), (42725659506729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672386691/5000000000 : ℝ)|^8333 ≤ (4357863664361/10000000000000 : ℝ)^6285
        have hw : |(2672386691/5000000000 : ℝ)|=(2672386691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55811781/250000000 : ℝ)|^8333 ≤ (13695703837491/100000000000000 : ℝ)^6285
        have hw : |(-55811781/250000000 : ℝ)|=(55811781/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053135683/2000000000 : ℝ)|^8333 ≤ (42725659506729/100000000000000 : ℝ)^6285
        have hw : |(1053135683/2000000000 : ℝ)|=(1053135683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672386737/5000000000 : ℝ)*x 0 + (5265678321/10000000000 : ℝ)*x 1 + (-1116235621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672386737/5000000000 : ℝ)^8333 ≤ (10894659409541/25000000000000 : ℝ)^6285 := by
    have hnat : (2672386737 : ℕ)^8333*25000000000000^6285 ≤ 10894659409541^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672386737 5000000000 10894659409541 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265678321/10000000000 : ℝ)^8333 ≤ (42725658495479/100000000000000 : ℝ)^6285 := by
    have hnat : (5265678321 : ℕ)^8333*100000000000000^6285 ≤ 42725658495479^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265678321 10000000000 42725658495479 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1116235621/5000000000 : ℝ)^8333 ≤ (13695703853759/100000000000000 : ℝ)^6285 := by
    have hnat : (1116235621 : ℕ)^8333*100000000000000^6285 ≤ 13695703853759^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116235621 5000000000 13695703853759 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672386737/5000000000 : ℝ), (5265678321/10000000000 : ℝ), (-1116235621/5000000000 : ℝ)] ![(10894659409541/25000000000000 : ℝ), (42725658495479/100000000000000 : ℝ), (13695703853759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672386737/5000000000 : ℝ)|^8333 ≤ (10894659409541/25000000000000 : ℝ)^6285
        have hw : |(2672386737/5000000000 : ℝ)|=(2672386737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265678321/10000000000 : ℝ)|^8333 ≤ (42725658495479/100000000000000 : ℝ)^6285
        have hw : |(5265678321/10000000000 : ℝ)|=(5265678321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1116235621/5000000000 : ℝ)|^8333 ≤ (13695703853759/100000000000000 : ℝ)^6285
        have hw : |(-1116235621/5000000000 : ℝ)|=(1116235621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364953577/10000000000 : ℝ)*x 0 + (1060020401/2500000000 : ℝ)*x 1 + (4493486581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364953577/10000000000 : ℝ)^8333 ≤ (6663388132291/20000000000000 : ℝ)^6285 := by
    have hnat : (4364953577 : ℕ)^8333*20000000000000^6285 ≤ 6663388132291^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364953577 10000000000 6663388132291 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060020401/2500000000 : ℝ)^8333 ≤ (32059161650129/100000000000000 : ℝ)^6285 := by
    have hnat : (1060020401 : ℕ)^8333*100000000000000^6285 ≤ 32059161650129^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060020401 2500000000 32059161650129 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493486581/10000000000 : ℝ)^8333 ≤ (17311948838909/50000000000000 : ℝ)^6285 := by
    have hnat : (4493486581 : ℕ)^8333*50000000000000^6285 ≤ 17311948838909^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493486581 10000000000 17311948838909 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364953577/10000000000 : ℝ), (1060020401/2500000000 : ℝ), (4493486581/10000000000 : ℝ)] ![(6663388132291/20000000000000 : ℝ), (32059161650129/100000000000000 : ℝ), (17311948838909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364953577/10000000000 : ℝ)|^8333 ≤ (6663388132291/20000000000000 : ℝ)^6285
        have hw : |(4364953577/10000000000 : ℝ)|=(4364953577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060020401/2500000000 : ℝ)|^8333 ≤ (32059161650129/100000000000000 : ℝ)^6285
        have hw : |(1060020401/2500000000 : ℝ)|=(1060020401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493486581/10000000000 : ℝ)|^8333 ≤ (17311948838909/50000000000000 : ℝ)^6285
        have hw : |(4493486581/10000000000 : ℝ)|=(4493486581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167844203/10000000000 : ℝ)*x 0 + (5265998631/10000000000 : ℝ)*x 1 + (5392779729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167844203/10000000000 : ℝ)^8333 ≤ (13172534763089/100000000000000 : ℝ)^6285 := by
    have hnat : (2167844203 : ℕ)^8333*100000000000000^6285 ≤ 13172534763089^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167844203 10000000000 13172534763089 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265998631/10000000000 : ℝ)^8333 ≤ (42729104416677/100000000000000 : ℝ)^6285 := by
    have hnat : (5265998631 : ℕ)^8333*100000000000000^6285 ≤ 42729104416677^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265998631 10000000000 42729104416677 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392779729/10000000000 : ℝ)^8333 ≤ (4409836080893/10000000000000 : ℝ)^6285 := by
    have hnat : (5392779729 : ℕ)^8333*10000000000000^6285 ≤ 4409836080893^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392779729 10000000000 4409836080893 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167844203/10000000000 : ℝ), (5265998631/10000000000 : ℝ), (5392779729/10000000000 : ℝ)] ![(13172534763089/100000000000000 : ℝ), (42729104416677/100000000000000 : ℝ), (4409836080893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167844203/10000000000 : ℝ)|^8333 ≤ (13172534763089/100000000000000 : ℝ)^6285
        have hw : |(-2167844203/10000000000 : ℝ)|=(2167844203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265998631/10000000000 : ℝ)|^8333 ≤ (42729104416677/100000000000000 : ℝ)^6285
        have hw : |(5265998631/10000000000 : ℝ)|=(5265998631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392779729/10000000000 : ℝ)|^8333 ≤ (4409836080893/10000000000000 : ℝ)^6285
        have hw : |(5392779729/10000000000 : ℝ)|=(5392779729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656247499/5000000000 : ℝ)*x 0 + (-1052684963/5000000000 : ℝ)*x 1 + (2696389863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656247499/5000000000 : ℝ)^8333 ≤ (43230039273357/100000000000000 : ℝ)^6285 := by
    have hnat : (2656247499 : ℕ)^8333*100000000000000^6285 ≤ 43230039273357^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656247499 5000000000 43230039273357 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052684963/5000000000 : ℝ)^8333 ≤ (12671599934953/100000000000000 : ℝ)^6285 := by
    have hnat : (1052684963 : ℕ)^8333*100000000000000^6285 ≤ 12671599934953^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052684963 5000000000 12671599934953 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696389863/5000000000 : ℝ)^8333 ≤ (11024590194101/25000000000000 : ℝ)^6285 := by
    have hnat : (2696389863 : ℕ)^8333*25000000000000^6285 ≤ 11024590194101^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696389863 5000000000 11024590194101 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656247499/5000000000 : ℝ), (-1052684963/5000000000 : ℝ), (2696389863/5000000000 : ℝ)] ![(43230039273357/100000000000000 : ℝ), (12671599934953/100000000000000 : ℝ), (11024590194101/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656247499/5000000000 : ℝ)|^8333 ≤ (43230039273357/100000000000000 : ℝ)^6285
        have hw : |(2656247499/5000000000 : ℝ)|=(2656247499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1052684963/5000000000 : ℝ)|^8333 ≤ (12671599934953/100000000000000 : ℝ)^6285
        have hw : |(-1052684963/5000000000 : ℝ)|=(1052684963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696389863/5000000000 : ℝ)|^8333 ≤ (11024590194101/25000000000000 : ℝ)^6285
        have hw : |(2696389863/5000000000 : ℝ)|=(2696389863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312494997/10000000000 : ℝ)*x 0 + (5392779729/10000000000 : ℝ)*x 1 + (-526342481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312494997/10000000000 : ℝ)^8333 ≤ (5403754907821/12500000000000 : ℝ)^6285 := by
    have hnat : (5312494997 : ℕ)^8333*12500000000000^6285 ≤ 5403754907821^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312494997 10000000000 5403754907821 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392779729/10000000000 : ℝ)^8333 ≤ (4409836080893/10000000000000 : ℝ)^6285 := by
    have hnat : (5392779729 : ℕ)^8333*10000000000000^6285 ≤ 4409836080893^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392779729 10000000000 4409836080893 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526342481/2500000000 : ℝ)^8333 ≤ (6335799959497/50000000000000 : ℝ)^6285 := by
    have hnat : (526342481 : ℕ)^8333*50000000000000^6285 ≤ 6335799959497^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526342481 2500000000 6335799959497 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312494997/10000000000 : ℝ), (5392779729/10000000000 : ℝ), (-526342481/2500000000 : ℝ)] ![(5403754907821/12500000000000 : ℝ), (4409836080893/10000000000000 : ℝ), (6335799959497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312494997/10000000000 : ℝ)|^8333 ≤ (5403754907821/12500000000000 : ℝ)^6285
        have hw : |(5312494997/10000000000 : ℝ)|=(5312494997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392779729/10000000000 : ℝ)|^8333 ≤ (4409836080893/10000000000000 : ℝ)^6285
        have hw : |(5392779729/10000000000 : ℝ)|=(5392779729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526342481/2500000000 : ℝ)|^8333 ≤ (6335799959497/50000000000000 : ℝ)^6285
        have hw : |(-526342481/2500000000 : ℝ)|=(526342481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s7_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872992631/2000000000 : ℝ)*x 0 + (2246424853/5000000000 : ℝ)*x 1 + (212036047/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872992631/2000000000 : ℝ)^8333 ≤ (33317037591089/100000000000000 : ℝ)^6285 := by
    have hnat : (872992631 : ℕ)^8333*100000000000000^6285 ≤ 33317037591089^6285*2000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872992631 2000000000 33317037591089 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246424853/5000000000 : ℝ)^8333 ≤ (17308695698691/50000000000000 : ℝ)^6285 := by
    have hnat : (2246424853 : ℕ)^8333*50000000000000^6285 ≤ 17308695698691^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246424853 5000000000 17308695698691 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212036047/500000000 : ℝ)^8333 ≤ (8016392749613/25000000000000 : ℝ)^6285 := by
    have hnat : (212036047 : ℕ)^8333*25000000000000^6285 ≤ 8016392749613^6285*500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212036047 500000000 8016392749613 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872992631/2000000000 : ℝ), (2246424853/5000000000 : ℝ), (212036047/500000000 : ℝ)] ![(33317037591089/100000000000000 : ℝ), (17308695698691/50000000000000 : ℝ), (8016392749613/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872992631/2000000000 : ℝ)|^8333 ≤ (33317037591089/100000000000000 : ℝ)^6285
        have hw : |(872992631/2000000000 : ℝ)|=(872992631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246424853/5000000000 : ℝ)|^8333 ≤ (17308695698691/50000000000000 : ℝ)^6285
        have hw : |(2246424853/5000000000 : ℝ)|=(2246424853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212036047/500000000 : ℝ)|^8333 ≤ (8016392749613/25000000000000 : ℝ)^6285
        have hw : |(212036047/500000000 : ℝ)|=(212036047/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (227/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1757/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1757/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11343/100000 : ℝ) ^ (2083/512 : ℝ) ≤ (222901785127199/1562500000000000000 : ℝ) := by
    have hpowers : (11343/100000 : ℝ)^2083 ≤ (222901785127199/1562500000000000000 : ℝ)^512 := by
      have hnat : (11343 : ℕ)^2083*1562500000000000000^512 ≤ 222901785127199^512*100000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11343 100000 222901785127199 1562500000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11343/100000 : ℝ)) (X := (222901785127199/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1757/12500 : ℝ) ^ (2083/512 : ℝ) ≤ (34134642257676037/100000000000000000000 : ℝ) := by
    have hpowers : (1757/12500 : ℝ)^2083 ≤ (34134642257676037/100000000000000000000 : ℝ)^512 := by
      have hnat : (1757 : ℕ)^2083*100000000000000000000^512 ≤ 34134642257676037^512*12500^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1757 12500 34134642257676037 100000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1757/12500 : ℝ)) (X := (34134642257676037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (781472901785127199/781250000000000000 : ℝ) ≤ (10000701225152993/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (781472901785127199/781250000000000000 : ℝ)^512 ≤ (10000701225152993/10000000000000000 : ℝ)^2083 := by
      have hnat : (781472901785127199 : ℕ)^512*10000000000000000^2083 ≤ 10000701225152993^2083*781250000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781472901785127199 781250000000000000 10000701225152993 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000701225152993/10000000000000000 : ℝ)) (X := (781472901785127199/781250000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048400356505816773/100000000000000000000 : ℝ) ≤ (625074341277117/625000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (100048400356505816773/100000000000000000000 : ℝ)^512 ≤ (625074341277117/625000000000000 : ℝ)^2083 := by
      have hnat : (100048400356505816773 : ℕ)^512*625000000000000^2083 ≤ 625074341277117^2083*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048400356505816773 100000000000000000000 625074341277117 625000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074341277117/625000000000000 : ℝ)) (X := (100048400356505816773/100000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034134642257676037/50000000000000000000 : ℝ) ≤ (10001677695714751/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (50034134642257676037/50000000000000000000 : ℝ)^512 ≤ (10001677695714751/10000000000000000 : ℝ)^2083 := by
      have hnat : (50034134642257676037 : ℕ)^512*10000000000000000^2083 ≤ 10001677695714751^2083*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034134642257676037 50000000000000000000 10001677695714751 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001677695714751/10000000000000000 : ℝ)) (X := (50034134642257676037/50000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(222901785127199/1562500000000000000 : ℝ) ≤ ((5424165263651609803/5426000000000000000 : ℝ)+2*(488235280879/271300000000000 : ℝ)*(11343/100000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (5424165263651609803/5426000000000000000 : ℝ)+2*(488235280879/271300000000000 : ℝ)*(11343/100000 : ℝ)=(10000701225152993/10000000000000000 : ℝ) by norm_num, show 1+2*(222901785127199/1562500000000000000 : ℝ)=(781472901785127199/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34134642257676037/100000000000000000000 : ℝ)+(222901785127199/1562500000000000000 : ℝ) ≤ ((5424165263651609803/5426000000000000000 : ℝ)+(488235280879/271300000000000 : ℝ)*((1757/12500 : ℝ)+(11343/100000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (5424165263651609803/5426000000000000000 : ℝ)+(488235280879/271300000000000 : ℝ)*((1757/12500 : ℝ)+(11343/100000 : ℝ))=(625074341277117/625000000000000 : ℝ) by norm_num, show 1+(34134642257676037/100000000000000000000 : ℝ)+(222901785127199/1562500000000000000 : ℝ)=(100048400356505816773/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34134642257676037/100000000000000000000 : ℝ) ≤ ((5424165263651609803/5426000000000000000 : ℝ)+2*(488235280879/271300000000000 : ℝ)*(1757/12500 : ℝ))^(2083/512 : ℝ) := by
    rw [show (5424165263651609803/5426000000000000000 : ℝ)+2*(488235280879/271300000000000 : ℝ)*(1757/12500 : ℝ)=(10001677695714751/10000000000000000 : ℝ) by norm_num, show 1+2*(34134642257676037/100000000000000000000 : ℝ)=(50034134642257676037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5424165263651609803/5426000000000000000 : ℝ)*(X 1 0+X 2 0)+(488235280879/271300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (5424165263651609803/5426000000000000000 : ℝ)) (alpha := (488235280879/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5424165263651609803/5426000000000000000 : ℝ)*(X 0 1+X 2 1)+(488235280879/271300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (5424165263651609803/5426000000000000000 : ℝ)) (alpha := (488235280879/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5424165263651609803/5426000000000000000 : ℝ)*(X 0 2+X 1 2)+(488235280879/271300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (11343/100000 : ℝ)) (hi := (1757/12500 : ℝ)) (c := (5424165263651609803/5426000000000000000 : ℝ)) (alpha := (488235280879/271300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1083919753/5000000000 : ℝ)*X 0 0+(5393101111/10000000000 : ℝ)*X 0 1+(5265678259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672386691/5000000000 : ℝ)*X 1 0+(-55811781/250000000 : ℝ)*X 1 1+(1053135683/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672386737/5000000000 : ℝ)*X 2 0+(5265678321/10000000000 : ℝ)*X 2 1+(-1116235621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364953577/10000000000 : ℝ)*X 0 0+(1060020401/2500000000 : ℝ)*X 0 1+(4493486581/10000000000 : ℝ)*X 0 2+(4364953577/10000000000 : ℝ)*X 1 0+(1060020401/2500000000 : ℝ)*X 1 1+(4493486581/10000000000 : ℝ)*X 1 2+(4364953577/10000000000 : ℝ)*X 2 0+(1060020401/2500000000 : ℝ)*X 2 1+(4493486581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167844203/10000000000 : ℝ)*X 0 0+(5265998631/10000000000 : ℝ)*X 0 1+(5392779729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656247499/5000000000 : ℝ)*X 1 0+(-1052684963/5000000000 : ℝ)*X 1 1+(2696389863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312494997/10000000000 : ℝ)*X 2 0+(5392779729/10000000000 : ℝ)*X 2 1+(-526342481/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872992631/2000000000 : ℝ)*X 0 0+(2246424853/5000000000 : ℝ)*X 0 1+(212036047/500000000 : ℝ)*X 0 2+(872992631/2000000000 : ℝ)*X 1 0+(2246424853/5000000000 : ℝ)*X 1 1+(212036047/500000000 : ℝ)*X 1 2+(872992631/2000000000 : ℝ)*X 2 0+(2246424853/5000000000 : ℝ)*X 2 1+(212036047/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (730051489522613905294612089/271300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1168233609/100000000000000 : ℝ)*(base19) + (1170503091/100000000000000 : ℝ)*(base23) + (100954911/50000000000000 : ℝ)*(upper3) + (70988237/100000000000000 : ℝ)*(upper4) + (127697313/100000000000000 : ℝ)*(upper5) + (5897124754590521/100000000000000 : ℝ)*(major0) + (5897124754590521/100000000000000 : ℝ)*(major1) + (5897124754590521/100000000000000 : ℝ)*(major2) + (313916922594413/4000000000000 : ℝ)*(sp0) + (980994894751839/12500000000000 : ℝ)*(sp1) + (784795915574523/10000000000000 : ℝ)*(sp2) + (1973134627989421/50000000000000 : ℝ)*(sp3) + (37261387997/100000000000000 : ℝ)*(sp4) + (1983725593/10000000000000 : ℝ)*(sp7) + (986572273308693/25000000000000 : ℝ)*(f.failure) + (7847960326248321/100000000000000 : ℝ)*(f.sum) + (1441250745459/3391250000000000000000000000 : ℝ)*base66 + (3623144607564342637/542600000000000000000000000000000 : ℝ)*base68 + (99580544920342637/542600000000000000000000000000000 : ℝ)*base70 + (5327364737743142637/542600000000000000000000000000000 : ℝ)*base72 + (6382890427461/13565000000000000000000000000 : ℝ)*base74 + (6204805027720457363/542600000000000000000000000000000 : ℝ)*base75 + (8227037063076742637/542600000000000000000000000000000 : ℝ)*base78 + (9925031727830857363/542600000000000000000000000000000 : ℝ)*base79 + (100840004277729/13565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (32165909/2500000000000000000000 : ℝ)*base90 + (32165909/2500000000000000000000 : ℝ)*base92 + (32165909/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52543836787999045342911/6782500000000000000000000000 : ℝ) := by norm_num
    linear_combination (699536649/50000000000000 : ℝ)*(base19) + (190938971/12500000000000 : ℝ)*(base23) + (19062549/12500000000000 : ℝ)*(upper3) + (5913047/10000000000000 : ℝ)*(lower4) + (31793629/20000000000000 : ℝ)*(upper5) + (5926918386669227/100000000000000 : ℝ)*(major0) + (5926918386669227/100000000000000 : ℝ)*(major1) + (5926918386669227/100000000000000 : ℝ)*(major2) + (770593487/2000000000000 : ℝ)*(sp1) + (41593885399/100000000000000 : ℝ)*(sp2) + (3943804930367743/50000000000000 : ℝ)*(sp4) + (3943784965993919/50000000000000 : ℝ)*(sp5) + (98594584241729/1250000000000 : ℝ)*(sp6) + (1983113327185283/50000000000000 : ℝ)*(sp7) + (1983113327185283/50000000000000 : ℝ)*(f.failure) + (3943804930367743/50000000000000 : ℝ)*(f.sum) + (60082223686147/13565000000000000000000000000 : ℝ)*base66 + (120856421918907719/542600000000000000000000000000000 : ℝ)*base68 + (769014950186107719/542600000000000000000000000000000 : ℝ)*base70 + (9166063530321892281/542600000000000000000000000000000 : ℝ)*base71 + (45696426371987/13565000000000000000000000000 : ℝ)*base74 + (3849941156759492281/542600000000000000000000000000000 : ℝ)*base75 + (114678840272692281/542600000000000000000000000000000 : ℝ)*base77 + (5933475575940707719/542600000000000000000000000000000 : ℝ)*base80 + (49107605988597/13565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6111421/5000000000000000000000 : ℝ)*base89 + (6111421/5000000000000000000000 : ℝ)*base91 + (6111421/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1140_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1757/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1140_s8_0 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-5419611/25000000 : ℝ)*x 0 + (2696515453/5000000000 : ℝ)*x 1 + (5265745347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5419611/25000000 : ℝ)^8333 ≤ (6586268175093/50000000000000 : ℝ)^6285 := by
    have hnat : (5419611 : ℕ)^8333*50000000000000^6285 ≤ 6586268175093^6285*25000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419611 25000000 6586268175093 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696515453/5000000000 : ℝ)^8333 ≤ (44101084068443/100000000000000 : ℝ)^6285 := by
    have hnat : (2696515453 : ℕ)^8333*100000000000000^6285 ≤ 44101084068443^6285*5000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696515453 5000000000 44101084068443 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265745347/10000000000 : ℝ)^8333 ≤ (21363189780511/50000000000000 : ℝ)^6285 := by
    have hnat : (5265745347 : ℕ)^8333*50000000000000^6285 ≤ 21363189780511^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265745347 10000000000 21363189780511 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5419611/25000000 : ℝ), (2696515453/5000000000 : ℝ), (5265745347/10000000000 : ℝ)] ![(6586268175093/50000000000000 : ℝ), (44101084068443/100000000000000 : ℝ), (21363189780511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5419611/25000000 : ℝ)|^8333 ≤ (6586268175093/50000000000000 : ℝ)^6285
        have hw : |(-5419611/25000000 : ℝ)|=(5419611/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696515453/5000000000 : ℝ)|^8333 ≤ (44101084068443/100000000000000 : ℝ)^6285
        have hw : |(2696515453/5000000000 : ℝ)|=(2696515453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265745347/10000000000 : ℝ)|^8333 ≤ (21363189780511/50000000000000 : ℝ)^6285
        have hw : |(5265745347/10000000000 : ℝ)|=(5265745347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_1 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213790241/400000000 : ℝ)*x 0 + (-2232405761/10000000000 : ℝ)*x 1 + (5265745363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213790241/400000000 : ℝ)^8333 ≤ (5447306126021/12500000000000 : ℝ)^6285 := by
    have hnat : (213790241 : ℕ)^8333*12500000000000^6285 ≤ 5447306126021^6285*400000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213790241 400000000 5447306126021 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2232405761/10000000000 : ℝ)^8333 ≤ (2739034249121/20000000000000 : ℝ)^6285 := by
    have hnat : (2232405761 : ℕ)^8333*20000000000000^6285 ≤ 2739034249121^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232405761 10000000000 2739034249121 20000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265745363/10000000000 : ℝ)^8333 ≤ (42726379733151/100000000000000 : ℝ)^6285 := by
    have hnat : (5265745363 : ℕ)^8333*100000000000000^6285 ≤ 42726379733151^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265745363 10000000000 42726379733151 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213790241/400000000 : ℝ), (-2232405761/10000000000 : ℝ), (5265745363/10000000000 : ℝ)] ![(5447306126021/12500000000000 : ℝ), (2739034249121/20000000000000 : ℝ), (42726379733151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213790241/400000000 : ℝ)|^8333 ≤ (5447306126021/12500000000000 : ℝ)^6285
        have hw : |(213790241/400000000 : ℝ)|=(213790241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2232405761/10000000000 : ℝ)|^8333 ≤ (2739034249121/20000000000000 : ℝ)^6285
        have hw : |(-2232405761/10000000000 : ℝ)|=(2232405761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265745363/10000000000 : ℝ)|^8333 ≤ (42726379733151/100000000000000 : ℝ)^6285
        have hw : |(5265745363/10000000000 : ℝ)|=(5265745363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_2 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344756023/10000000000 : ℝ)*x 0 + (5265745357/10000000000 : ℝ)*x 1 + (-558101443/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344756023/10000000000 : ℝ)^8333 ≤ (43578448986547/100000000000000 : ℝ)^6285 := by
    have hnat : (5344756023 : ℕ)^8333*100000000000000^6285 ≤ 43578448986547^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344756023 10000000000 43578448986547 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265745357/10000000000 : ℝ)^8333 ≤ (42726379668603/100000000000000 : ℝ)^6285 := by
    have hnat : (5265745357 : ℕ)^8333*100000000000000^6285 ≤ 42726379668603^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265745357 10000000000 42726379668603 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558101443/2500000000 : ℝ)^8333 ≤ (3423792833769/25000000000000 : ℝ)^6285 := by
    have hnat : (558101443 : ℕ)^8333*25000000000000^6285 ≤ 3423792833769^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558101443 2500000000 3423792833769 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344756023/10000000000 : ℝ), (5265745357/10000000000 : ℝ), (-558101443/2500000000 : ℝ)] ![(43578448986547/100000000000000 : ℝ), (42726379668603/100000000000000 : ℝ), (3423792833769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344756023/10000000000 : ℝ)|^8333 ≤ (43578448986547/100000000000000 : ℝ)^6285
        have hw : |(5344756023/10000000000 : ℝ)|=(5344756023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265745357/10000000000 : ℝ)|^8333 ≤ (42726379668603/100000000000000 : ℝ)^6285
        have hw : |(5265745357/10000000000 : ℝ)|=(5265745357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558101443/2500000000 : ℝ)|^8333 ≤ (3423792833769/25000000000000 : ℝ)^6285
        have hw : |(-558101443/2500000000 : ℝ)|=(558101443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_3 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272809807/625000000 : ℝ)*x 0 + (4240217723/10000000000 : ℝ)*x 1 + (1123337427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272809807/625000000 : ℝ)^8333 ≤ (16658487205871/50000000000000 : ℝ)^6285 := by
    have hnat : (272809807 : ℕ)^8333*50000000000000^6285 ≤ 16658487205871^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272809807 625000000 16658487205871 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240217723/10000000000 : ℝ)^8333 ≤ (4007565777221/12500000000000 : ℝ)^6285 := by
    have hnat : (4240217723 : ℕ)^8333*12500000000000^6285 ≤ 4007565777221^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240217723 10000000000 4007565777221 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123337427/2500000000 : ℝ)^8333 ≤ (34622499365327/100000000000000 : ℝ)^6285 := by
    have hnat : (1123337427 : ℕ)^8333*100000000000000^6285 ≤ 34622499365327^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123337427 2500000000 34622499365327 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272809807/625000000 : ℝ), (4240217723/10000000000 : ℝ), (1123337427/2500000000 : ℝ)] ![(16658487205871/50000000000000 : ℝ), (4007565777221/12500000000000 : ℝ), (34622499365327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272809807/625000000 : ℝ)|^8333 ≤ (16658487205871/50000000000000 : ℝ)^6285
        have hw : |(272809807/625000000 : ℝ)|=(272809807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240217723/10000000000 : ℝ)|^8333 ≤ (4007565777221/12500000000000 : ℝ)^6285
        have hw : |(4240217723/10000000000 : ℝ)|=(4240217723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123337427/2500000000 : ℝ)|^8333 ≤ (34622499365327/100000000000000 : ℝ)^6285
        have hw : |(1123337427/2500000000 : ℝ)|=(1123337427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_4 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-541962343/2500000000 : ℝ)*x 0 + (5266064833/10000000000 : ℝ)*x 1 + (5392710197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541962343/2500000000 : ℝ)^8333 ≤ (823286025393/6250000000000 : ℝ)^6285 := by
    have hnat : (541962343 : ℕ)^8333*6250000000000^6285 ≤ 823286025393^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541962343 2500000000 823286025393 6250000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266064833/10000000000 : ℝ)^8333 ≤ (2670613539483/6250000000000 : ℝ)^6285 := by
    have hnat : (5266064833 : ℕ)^8333*6250000000000^6285 ≤ 2670613539483^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266064833 10000000000 2670613539483 6250000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392710197/10000000000 : ℝ)^8333 ≤ (5512200868839/12500000000000 : ℝ)^6285 := by
    have hnat : (5392710197 : ℕ)^8333*12500000000000^6285 ≤ 5512200868839^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392710197 10000000000 5512200868839 12500000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541962343/2500000000 : ℝ), (5266064833/10000000000 : ℝ), (5392710197/10000000000 : ℝ)] ![(823286025393/6250000000000 : ℝ), (2670613539483/6250000000000 : ℝ), (5512200868839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541962343/2500000000 : ℝ)|^8333 ≤ (823286025393/6250000000000 : ℝ)^6285
        have hw : |(-541962343/2500000000 : ℝ)|=(541962343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266064833/10000000000 : ℝ)|^8333 ≤ (2670613539483/6250000000000 : ℝ)^6285
        have hw : |(5266064833/10000000000 : ℝ)|=(5266064833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392710197/10000000000 : ℝ)|^8333 ≤ (5512200868839/12500000000000 : ℝ)^6285
        have hw : |(5392710197/10000000000 : ℝ)|=(5392710197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_5 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328128087/2500000000 : ℝ)*x 0 + (-2105440917/10000000000 : ℝ)*x 1 + (84261097/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328128087/2500000000 : ℝ)^8333 ≤ (4323022646347/10000000000000 : ℝ)^6285 := by
    have hnat : (1328128087 : ℕ)^8333*10000000000000^6285 ≤ 4323022646347^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328128087 2500000000 4323022646347 10000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105440917/10000000000 : ℝ)^8333 ≤ (12672166441349/100000000000000 : ℝ)^6285 := by
    have hnat : (2105440917 : ℕ)^8333*100000000000000^6285 ≤ 12672166441349^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105440917 10000000000 12672166441349 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84261097/156250000 : ℝ)^8333 ≤ (11024401767493/25000000000000 : ℝ)^6285 := by
    have hnat : (84261097 : ℕ)^8333*25000000000000^6285 ≤ 11024401767493^6285*156250000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84261097 156250000 11024401767493 25000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328128087/2500000000 : ℝ), (-2105440917/10000000000 : ℝ), (84261097/156250000 : ℝ)] ![(4323022646347/10000000000000 : ℝ), (12672166441349/100000000000000 : ℝ), (11024401767493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328128087/2500000000 : ℝ)|^8333 ≤ (4323022646347/10000000000000 : ℝ)^6285
        have hw : |(1328128087/2500000000 : ℝ)|=(1328128087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105440917/10000000000 : ℝ)|^8333 ≤ (12672166441349/100000000000000 : ℝ)^6285
        have hw : |(-2105440917/10000000000 : ℝ)|=(2105440917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84261097/156250000 : ℝ)|^8333 ≤ (11024401767493/25000000000000 : ℝ)^6285
        have hw : |(84261097/156250000 : ℝ)|=(84261097/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_6 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166016007/312500000 : ℝ)*x 0 + (337044387/625000000 : ℝ)*x 1 + (-526360277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166016007/312500000 : ℝ)^8333 ≤ (21615112562813/50000000000000 : ℝ)^6285 := by
    have hnat : (166016007 : ℕ)^8333*50000000000000^6285 ≤ 21615112562813^6285*312500000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166016007 312500000 21615112562813 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337044387/625000000 : ℝ)^8333 ≤ (22048803448251/50000000000000 : ℝ)^6285 := by
    have hnat : (337044387 : ℕ)^8333*50000000000000^6285 ≤ 22048803448251^6285*625000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337044387 625000000 22048803448251 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526360277/2500000000 : ℝ)^8333 ≤ (12672167965533/100000000000000 : ℝ)^6285 := by
    have hnat : (526360277 : ℕ)^8333*100000000000000^6285 ≤ 12672167965533^6285*2500000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526360277 2500000000 12672167965533 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166016007/312500000 : ℝ), (337044387/625000000 : ℝ), (-526360277/2500000000 : ℝ)] ![(21615112562813/50000000000000 : ℝ), (22048803448251/50000000000000 : ℝ), (12672167965533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166016007/312500000 : ℝ)|^8333 ≤ (21615112562813/50000000000000 : ℝ)^6285
        have hw : |(166016007/312500000 : ℝ)|=(166016007/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337044387/625000000 : ℝ)|^8333 ≤ (22048803448251/50000000000000 : ℝ)^6285
        have hw : |(337044387/625000000 : ℝ)|=(337044387/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526360277/2500000000 : ℝ)|^8333 ≤ (12672167965533/100000000000000 : ℝ)^6285
        have hw : |(-526360277/2500000000 : ℝ)|=(526360277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1140_s8_7 (p : ℝ) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364966539/10000000000 : ℝ)*x 0 + (4492714203/10000000000 : ℝ)*x 1 + (4240855599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364966539/10000000000 : ℝ)^8333 ≤ (16658535918641/50000000000000 : ℝ)^6285 := by
    have hnat : (4364966539 : ℕ)^8333*50000000000000^6285 ≤ 16658535918641^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364966539 10000000000 16658535918641 50000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492714203/10000000000 : ℝ)^8333 ≤ (1730800357243/5000000000000 : ℝ)^6285 := by
    have hnat : (4492714203 : ℕ)^8333*5000000000000^6285 ≤ 1730800357243^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492714203 10000000000 1730800357243 5000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240855599/10000000000 : ℝ)^8333 ≤ (32066920996109/100000000000000 : ℝ)^6285 := by
    have hnat : (4240855599 : ℕ)^8333*100000000000000^6285 ≤ 32066920996109^6285*10000000000^8333 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240855599 10000000000 32066920996109 100000000000000 8333 6285 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8333/2048 : ℝ)) 8333 6285 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364966539/10000000000 : ℝ), (4492714203/10000000000 : ℝ), (4240855599/10000000000 : ℝ)] ![(16658535918641/50000000000000 : ℝ), (1730800357243/5000000000000 : ℝ), (32066920996109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364966539/10000000000 : ℝ)|^8333 ≤ (16658535918641/50000000000000 : ℝ)^6285
        have hw : |(4364966539/10000000000 : ℝ)|=(4364966539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492714203/10000000000 : ℝ)|^8333 ≤ (1730800357243/5000000000000 : ℝ)^6285
        have hw : |(4492714203/10000000000 : ℝ)|=(4492714203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240855599/10000000000 : ℝ)|^8333 ≤ (32066920996109/100000000000000 : ℝ)^6285
        have hw : |(4240855599/10000000000 : ℝ)|=(4240855599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1140_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (11351/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (227/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (227/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (227/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (227/2000 : ℝ) ^ (2083/512 : ℝ) ≤ (14301564655638297/100000000000000000000 : ℝ) := by
    have hpowers : (227/2000 : ℝ)^2083 ≤ (14301564655638297/100000000000000000000 : ℝ)^512 := by
      have hnat : (227 : ℕ)^2083*100000000000000000000^512 ≤ 14301564655638297^512*2000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        227 2000 14301564655638297 100000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (227/2000 : ℝ)) (X := (14301564655638297/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (2083/512 : ℝ) ≤ (8516383930282529/25000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^2083 ≤ (8516383930282529/25000000000000000000 : ℝ)^512 := by
      have hnat : (14049 : ℕ)^2083*25000000000000000000^512 ≤ 8516383930282529^512*100000^2083 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 8516383930282529 25000000000000000000 2083 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (8516383930282529/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014301564655638297/50000000000000000000 : ℝ) ≤ (2000140597434917/2000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (50014301564655638297/50000000000000000000 : ℝ)^512 ≤ (2000140597434917/2000000000000000 : ℝ)^2083 := by
      have hnat : (50014301564655638297 : ℕ)^512*2000000000000000^2083 ≤ 2000140597434917^2083*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014301564655638297 50000000000000000000 2000140597434917 2000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000140597434917/2000000000000000 : ℝ)) (X := (50014301564655638297/50000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048367100376768413/100000000000000000000 : ℝ) ≤ (10001188643298619/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (100048367100376768413/100000000000000000000 : ℝ)^512 ≤ (10001188643298619/10000000000000000 : ℝ)^2083 := by
      have hnat : (100048367100376768413 : ℕ)^512*10000000000000000^2083 ≤ 10001188643298619^2083*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048367100376768413 100000000000000000000 10001188643298619 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001188643298619/10000000000000000 : ℝ)) (X := (100048367100376768413/100000000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508516383930282529/12500000000000000000 : ℝ) ≤ (10001674299422653/10000000000000000 : ℝ) ^ (2083/512 : ℝ) := by
    have hpowers : (12508516383930282529/12500000000000000000 : ℝ)^512 ≤ (10001674299422653/10000000000000000 : ℝ)^2083 := by
      have hnat : (12508516383930282529 : ℕ)^512*10000000000000000^2083 ≤ 10001674299422653^2083*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508516383930282529 12500000000000000000 10001674299422653 10000000000000000 512 2083 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001674299422653/10000000000000000 : ℝ)) (X := (12508516383930282529/12500000000000000000 : ℝ)) (by norm_num) 2083 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14301564655638297/100000000000000000000 : ℝ) ≤ ((5396174593673726623/5398000000000000000 : ℝ)+2*(242828062017/134950000000000 : ℝ)*(227/2000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (5396174593673726623/5398000000000000000 : ℝ)+2*(242828062017/134950000000000 : ℝ)*(227/2000 : ℝ)=(2000140597434917/2000000000000000 : ℝ) by norm_num, show 1+2*(14301564655638297/100000000000000000000 : ℝ)=(50014301564655638297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8516383930282529/25000000000000000000 : ℝ)+(14301564655638297/100000000000000000000 : ℝ) ≤ ((5396174593673726623/5398000000000000000 : ℝ)+(242828062017/134950000000000 : ℝ)*((14049/100000 : ℝ)+(227/2000 : ℝ)))^(2083/512 : ℝ) := by
    rw [show (5396174593673726623/5398000000000000000 : ℝ)+(242828062017/134950000000000 : ℝ)*((14049/100000 : ℝ)+(227/2000 : ℝ))=(10001188643298619/10000000000000000 : ℝ) by norm_num, show 1+(8516383930282529/25000000000000000000 : ℝ)+(14301564655638297/100000000000000000000 : ℝ)=(100048367100376768413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8516383930282529/25000000000000000000 : ℝ) ≤ ((5396174593673726623/5398000000000000000 : ℝ)+2*(242828062017/134950000000000 : ℝ)*(14049/100000 : ℝ))^(2083/512 : ℝ) := by
    rw [show (5396174593673726623/5398000000000000000 : ℝ)+2*(242828062017/134950000000000 : ℝ)*(14049/100000 : ℝ)=(10001674299422653/10000000000000000 : ℝ) by norm_num, show 1+2*(8516383930282529/25000000000000000000 : ℝ)=(12508516383930282529/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5396174593673726623/5398000000000000000 : ℝ)*(X 1 0+X 2 0)+(242828062017/134950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (5396174593673726623/5398000000000000000 : ℝ)) (alpha := (242828062017/134950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5396174593673726623/5398000000000000000 : ℝ)*(X 0 1+X 2 1)+(242828062017/134950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (5396174593673726623/5398000000000000000 : ℝ)) (alpha := (242828062017/134950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5396174593673726623/5398000000000000000 : ℝ)*(X 0 2+X 1 2)+(242828062017/134950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2083/512 : ℝ)) (lo := (227/2000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (5396174593673726623/5398000000000000000 : ℝ)) (alpha := (242828062017/134950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-5419611/25000000 : ℝ)*X 0 0+(2696515453/5000000000 : ℝ)*X 0 1+(5265745347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213790241/400000000 : ℝ)*X 1 0+(-2232405761/10000000000 : ℝ)*X 1 1+(5265745363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344756023/10000000000 : ℝ)*X 2 0+(5265745357/10000000000 : ℝ)*X 2 1+(-558101443/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272809807/625000000 : ℝ)*X 0 0+(4240217723/10000000000 : ℝ)*X 0 1+(1123337427/2500000000 : ℝ)*X 0 2+(272809807/625000000 : ℝ)*X 1 0+(4240217723/10000000000 : ℝ)*X 1 1+(1123337427/2500000000 : ℝ)*X 1 2+(272809807/625000000 : ℝ)*X 2 0+(4240217723/10000000000 : ℝ)*X 2 1+(1123337427/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-541962343/2500000000 : ℝ)*X 0 0+(5266064833/10000000000 : ℝ)*X 0 1+(5392710197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328128087/2500000000 : ℝ)*X 1 0+(-2105440917/10000000000 : ℝ)*X 1 1+(84261097/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166016007/312500000 : ℝ)*X 2 0+(337044387/625000000 : ℝ)*X 2 1+(-526360277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364966539/10000000000 : ℝ)*X 0 0+(4492714203/10000000000 : ℝ)*X 0 1+(4240855599/10000000000 : ℝ)*X 0 2+(4364966539/10000000000 : ℝ)*X 1 0+(4492714203/10000000000 : ℝ)*X 1 1+(4240855599/10000000000 : ℝ)*X 1 2+(4364966539/10000000000 : ℝ)*X 2 0+(4492714203/10000000000 : ℝ)*X 2 1+(4240855599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1140_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1096121305731436437210605397/134950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (322193197/20000000000000 : ℝ)*(base19) + (1510297129/100000000000000 : ℝ)*(base23) + (326461/625000000000 : ℝ)*(lower2) + (216300957/100000000000000 : ℝ)*(upper3) + (15757939/12500000000000 : ℝ)*(upper5) + (236139915247673/4000000000000 : ℝ)*(major0) + (236139915247673/4000000000000 : ℝ)*(major1) + (2951748940595913/50000000000000 : ℝ)*(major2) + (7856397550924439/100000000000000 : ℝ)*(sp0) + (1964109990824413/25000000000000 : ℝ)*(sp1) + (1964110015991627/25000000000000 : ℝ)*(sp2) + (1975264932547381/50000000000000 : ℝ)*(sp3) + (22011669599/50000000000000 : ℝ)*(sp4) + (6013069433/25000000000000 : ℝ)*(sp7) + (1975276958686247/50000000000000 : ℝ)*(f.failure) + (7856441574263637/100000000000000 : ℝ)*(f.sum) + (44642555844247/13495000000000000000000000000 : ℝ)*base65 + (5906835566714521/21592000000000000000000000000000 : ℝ)*base68 + (1331443583686108201/269900000000000000000000000000000 : ℝ)*base70 + (60023740450901479/21592000000000000000000000000000 : ℝ)*base71 + (32818343265817/13495000000000000000000000000 : ℝ)*base73 + (7255897119642408201/269900000000000000000000000000000 : ℝ)*base76 + (178220112252346279/21592000000000000000000000000000 : ℝ)*base77 + (55710113985237721/21592000000000000000000000000000 : ℝ)*base80 + (659702701799/1349500000000000000000000000 : ℝ)*base81 + (1649689/5000000000000000000000 : ℝ)*base89 + (1649689/5000000000000000000000 : ℝ)*base91 + (48350311/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4045622587486357343289/1349500000000000000000000000 : ℝ) := by norm_num
    linear_combination (24564433/5000000000000 : ℝ)*(base19) + (397122453/100000000000000 : ℝ)*(base23) + (15959571/50000000000000 : ℝ)*(lower1) + (22093757/25000000000000 : ℝ)*(upper2) + (10920543/25000000000000 : ℝ)*(upper3) + (8532499/6250000000000 : ℝ)*(upper5) + (18541465510239/312500000000 : ℝ)*(major0) + (18541465510239/312500000000 : ℝ)*(major1) + (18541465510239/312500000000 : ℝ)*(major2) + (627871707/5000000000000 : ℝ)*(sp1) + (7896061438316337/100000000000000 : ℝ)*(sp4) + (3948024194796769/50000000000000 : ℝ)*(sp5) + (1974015260298471/25000000000000 : ℝ)*(sp6) + (992619097076919/25000000000000 : ℝ)*(sp7) + (992619097076919/25000000000000 : ℝ)*(f.failure) + (7896061438316337/100000000000000 : ℝ)*(f.sum) + (387364131617/337375000000000000000000000 : ℝ)*base66 + (3095957313090739/843437500000000000000000000000 : ℝ)*base68 + (66399018682085511/843437500000000000000000000000 : ℝ)*base69 + (16489207548717897/1686875000000000000000000000000 : ℝ)*base71 + (2908381895997/1349500000000000000000000000 : ℝ)*base74 + (19315477738432103/1686875000000000000000000000000 : ℝ)*base76 + (28850058579275397/1686875000000000000000000000000 : ℝ)*base77 + (38394002457364603/1686875000000000000000000000000 : ℝ)*base80 + (31307318864529/674750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5689353/2500000000000000000000 : ℝ)*base89 + (5689353/2500000000000000000000 : ℝ)*base91 + (5689353/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1140_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1140_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1140_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1140_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1140_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1140_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2083/512 : ℝ) ≤ p) (hpb : p ≤ (8333/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149434687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1140_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
