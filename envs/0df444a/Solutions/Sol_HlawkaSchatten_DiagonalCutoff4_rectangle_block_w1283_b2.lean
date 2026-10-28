-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1283_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:43.13572+00:00
-- url     : https://prove2.me/submissions/1924823e-9ce2-414b-aef4-2cc71fcc141f

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
theorem support_rectangle_w1283_s6_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419210609/2000000000 : ℝ)*x 0 + (216631717/400000000 : ℝ)*x 1 + (655321123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419210609/2000000000 : ℝ)^4243 ≤ (2550132325577/20000000000000 : ℝ)^3219 := by
    have hnat : (419210609 : ℕ)^4243*20000000000000^3219 ≤ 2550132325577^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419210609 2000000000 2550132325577 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216631717/400000000 : ℝ)^4243 ≤ (4455915658953/10000000000000 : ℝ)^3219 := by
    have hnat : (216631717 : ℕ)^4243*10000000000000^3219 ≤ 4455915658953^3219*400000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216631717 400000000 4455915658953 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655321123/1250000000 : ℝ)^4243 ≤ (83379261257/195312500000 : ℝ)^3219 := by
    have hnat : (655321123 : ℕ)^4243*195312500000^3219 ≤ 83379261257^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655321123 1250000000 83379261257 195312500000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419210609/2000000000 : ℝ), (216631717/400000000 : ℝ), (655321123/1250000000 : ℝ)] ![(2550132325577/20000000000000 : ℝ), (4455915658953/10000000000000 : ℝ), (83379261257/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419210609/2000000000 : ℝ)|^4243 ≤ (2550132325577/20000000000000 : ℝ)^3219
        have hw : |(-419210609/2000000000 : ℝ)|=(419210609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216631717/400000000 : ℝ)|^4243 ≤ (4455915658953/10000000000000 : ℝ)^3219
        have hw : |(216631717/400000000 : ℝ)|=(216631717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655321123/1250000000 : ℝ)|^4243 ≤ (83379261257/195312500000 : ℝ)^3219
        have hw : |(655321123/1250000000 : ℝ)|=(655321123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069987783/2000000000 : ℝ)*x 0 + (-1092181559/5000000000 : ℝ)*x 1 + (5242568973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069987783/2000000000 : ℝ)^4243 ≤ (43846359216573/100000000000000 : ℝ)^3219 := by
    have hnat : (1069987783 : ℕ)^4243*100000000000000^3219 ≤ 43846359216573^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069987783 2000000000 43846359216573 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092181559/5000000000 : ℝ)^4243 ≤ (13463459114857/100000000000000 : ℝ)^3219 := by
    have hnat : (1092181559 : ℕ)^4243*100000000000000^3219 ≤ 13463459114857^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092181559 5000000000 13463459114857 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242568973/10000000000 : ℝ)^4243 ≤ (42690181645517/100000000000000 : ℝ)^3219 := by
    have hnat : (5242568973 : ℕ)^4243*100000000000000^3219 ≤ 42690181645517^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242568973 10000000000 42690181645517 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069987783/2000000000 : ℝ), (-1092181559/5000000000 : ℝ), (5242568973/10000000000 : ℝ)] ![(43846359216573/100000000000000 : ℝ), (13463459114857/100000000000000 : ℝ), (42690181645517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069987783/2000000000 : ℝ)|^4243 ≤ (43846359216573/100000000000000 : ℝ)^3219
        have hw : |(1069987783/2000000000 : ℝ)|=(1069987783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092181559/5000000000 : ℝ)|^4243 ≤ (13463459114857/100000000000000 : ℝ)^3219
        have hw : |(-1092181559/5000000000 : ℝ)|=(1092181559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242568973/10000000000 : ℝ)|^4243 ≤ (42690181645517/100000000000000 : ℝ)^3219
        have hw : |(5242568973/10000000000 : ℝ)|=(5242568973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069987781/2000000000 : ℝ)*x 0 + (1310642243/2500000000 : ℝ)*x 1 + (-1092181567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069987781/2000000000 : ℝ)^4243 ≤ (8769271821709/20000000000000 : ℝ)^3219 := by
    have hnat : (1069987781 : ℕ)^4243*20000000000000^3219 ≤ 8769271821709^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069987781 2000000000 8769271821709 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310642243/2500000000 : ℝ)^4243 ≤ (42690181634783/100000000000000 : ℝ)^3219 := by
    have hnat : (1310642243 : ℕ)^4243*100000000000000^3219 ≤ 42690181634783^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310642243 2500000000 42690181634783 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092181567/5000000000 : ℝ)^4243 ≤ (6731729622423/50000000000000 : ℝ)^3219 := by
    have hnat : (1092181567 : ℕ)^4243*50000000000000^3219 ≤ 6731729622423^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092181567 5000000000 6731729622423 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069987781/2000000000 : ℝ), (1310642243/2500000000 : ℝ), (-1092181567/5000000000 : ℝ)] ![(8769271821709/20000000000000 : ℝ), (42690181634783/100000000000000 : ℝ), (6731729622423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069987781/2000000000 : ℝ)|^4243 ≤ (8769271821709/20000000000000 : ℝ)^3219
        have hw : |(1069987781/2000000000 : ℝ)|=(1069987781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310642243/2500000000 : ℝ)|^4243 ≤ (42690181634783/100000000000000 : ℝ)^3219
        have hw : |(1310642243/2500000000 : ℝ)|=(1310642243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092181567/5000000000 : ℝ)|^4243 ≤ (6731729622423/50000000000000 : ℝ)^3219
        have hw : |(-1092181567/5000000000 : ℝ)|=(1092181567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342281181/10000000000 : ℝ)*x 0 + (4168362981/10000000000 : ℝ)*x 1 + (1130788831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342281181/10000000000 : ℝ)^4243 ≤ (33302125799909/100000000000000 : ℝ)^3219 := by
    have hnat : (4342281181 : ℕ)^4243*100000000000000^3219 ≤ 33302125799909^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342281181 10000000000 33302125799909 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168362981/10000000000 : ℝ)^4243 ≤ (493051551267/1562500000000 : ℝ)^3219 := by
    have hnat : (4168362981 : ℕ)^4243*1562500000000^3219 ≤ 493051551267^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168362981 10000000000 493051551267 1562500000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130788831/2500000000 : ℝ)^4243 ≤ (17571287449119/50000000000000 : ℝ)^3219 := by
    have hnat : (1130788831 : ℕ)^4243*50000000000000^3219 ≤ 17571287449119^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130788831 2500000000 17571287449119 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342281181/10000000000 : ℝ), (4168362981/10000000000 : ℝ), (1130788831/2500000000 : ℝ)] ![(33302125799909/100000000000000 : ℝ), (493051551267/1562500000000 : ℝ), (17571287449119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342281181/10000000000 : ℝ)|^4243 ≤ (33302125799909/100000000000000 : ℝ)^3219
        have hw : |(4342281181/10000000000 : ℝ)|=(4342281181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168362981/10000000000 : ℝ)|^4243 ≤ (493051551267/1562500000000 : ℝ)^3219
        have hw : |(4168362981/10000000000 : ℝ)|=(4168362981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130788831/2500000000 : ℝ)|^4243 ≤ (17571287449119/50000000000000 : ℝ)^3219
        have hw : |(1130788831/2500000000 : ℝ)|=(1130788831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-524016477/2500000000 : ℝ)*x 0 + (2621593331/5000000000 : ℝ)*x 1 + (1353793017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524016477/2500000000 : ℝ)^4243 ≤ (3187691191857/25000000000000 : ℝ)^3219 := by
    have hnat : (524016477 : ℕ)^4243*25000000000000^3219 ≤ 3187691191857^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524016477 2500000000 3187691191857 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621593331/5000000000 : ℝ)^4243 ≤ (42696811651353/100000000000000 : ℝ)^3219 := by
    have hnat : (2621593331 : ℕ)^4243*100000000000000^3219 ≤ 42696811651353^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621593331 5000000000 42696811651353 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353793017/2500000000 : ℝ)^4243 ≤ (11138105889573/25000000000000 : ℝ)^3219 := by
    have hnat : (1353793017 : ℕ)^4243*25000000000000^3219 ≤ 11138105889573^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353793017 2500000000 11138105889573 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524016477/2500000000 : ℝ), (2621593331/5000000000 : ℝ), (1353793017/2500000000 : ℝ)] ![(3187691191857/25000000000000 : ℝ), (42696811651353/100000000000000 : ℝ), (11138105889573/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524016477/2500000000 : ℝ)|^4243 ≤ (3187691191857/25000000000000 : ℝ)^3219
        have hw : |(-524016477/2500000000 : ℝ)|=(524016477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621593331/5000000000 : ℝ)|^4243 ≤ (42696811651353/100000000000000 : ℝ)^3219
        have hw : |(2621593331/5000000000 : ℝ)|=(2621593331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353793017/2500000000 : ℝ)|^4243 ≤ (11138105889573/25000000000000 : ℝ)^3219
        have hw : |(1353793017/2500000000 : ℝ)|=(1353793017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305640013/10000000000 : ℝ)*x 0 + (-402352009/2000000000 : ℝ)*x 1 + (2707586043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305640013/10000000000 : ℝ)^4243 ≤ (8673687603037/20000000000000 : ℝ)^3219 := by
    have hnat : (5305640013 : ℕ)^4243*20000000000000^3219 ≤ 8673687603037^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305640013 10000000000 8673687603037 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402352009/2000000000 : ℝ)^4243 ≤ (6039569107899/50000000000000 : ℝ)^3219 := by
    have hnat : (402352009 : ℕ)^4243*50000000000000^3219 ≤ 6039569107899^3219*2000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402352009 2000000000 6039569107899 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707586043/5000000000 : ℝ)^4243 ≤ (22276211876747/50000000000000 : ℝ)^3219 := by
    have hnat : (2707586043 : ℕ)^4243*50000000000000^3219 ≤ 22276211876747^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707586043 5000000000 22276211876747 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305640013/10000000000 : ℝ), (-402352009/2000000000 : ℝ), (2707586043/5000000000 : ℝ)] ![(8673687603037/20000000000000 : ℝ), (6039569107899/50000000000000 : ℝ), (22276211876747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305640013/10000000000 : ℝ)|^4243 ≤ (8673687603037/20000000000000 : ℝ)^3219
        have hw : |(5305640013/10000000000 : ℝ)|=(5305640013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-402352009/2000000000 : ℝ)|^4243 ≤ (6039569107899/50000000000000 : ℝ)^3219
        have hw : |(-402352009/2000000000 : ℝ)|=(402352009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707586043/5000000000 : ℝ)|^4243 ≤ (22276211876747/50000000000000 : ℝ)^3219
        have hw : |(2707586043/5000000000 : ℝ)|=(2707586043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652820023/5000000000 : ℝ)*x 0 + (5415172057/10000000000 : ℝ)*x 1 + (-2011760039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652820023/5000000000 : ℝ)^4243 ≤ (2710527398171/6250000000000 : ℝ)^3219 := by
    have hnat : (2652820023 : ℕ)^4243*6250000000000^3219 ≤ 2710527398171^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652820023 5000000000 2710527398171 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415172057/10000000000 : ℝ)^4243 ≤ (22276211719501/50000000000000 : ℝ)^3219 := by
    have hnat : (5415172057 : ℕ)^4243*50000000000000^3219 ≤ 22276211719501^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415172057 10000000000 22276211719501 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011760039/10000000000 : ℝ)^4243 ≤ (1509892271039/12500000000000 : ℝ)^3219 := by
    have hnat : (2011760039 : ℕ)^4243*12500000000000^3219 ≤ 1509892271039^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011760039 10000000000 1509892271039 12500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652820023/5000000000 : ℝ), (5415172057/10000000000 : ℝ), (-2011760039/10000000000 : ℝ)] ![(2710527398171/6250000000000 : ℝ), (22276211719501/50000000000000 : ℝ), (1509892271039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652820023/5000000000 : ℝ)|^4243 ≤ (2710527398171/6250000000000 : ℝ)^3219
        have hw : |(2652820023/5000000000 : ℝ)|=(2652820023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415172057/10000000000 : ℝ)|^4243 ≤ (22276211719501/50000000000000 : ℝ)^3219
        have hw : |(5415172057/10000000000 : ℝ)|=(5415172057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011760039/10000000000 : ℝ)|^4243 ≤ (1509892271039/12500000000000 : ℝ)^3219
        have hw : |(-2011760039/10000000000 : ℝ)|=(2011760039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s6_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171153759/5000000000 : ℝ)*x 0 + (1130472551/2500000000 : ℝ)*x 1 + (2084817303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171153759/5000000000 : ℝ)^4243 ≤ (6660478407919/20000000000000 : ℝ)^3219 := by
    have hnat : (2171153759 : ℕ)^4243*20000000000000^3219 ≤ 6660478407919^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171153759 5000000000 6660478407919 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130472551/2500000000 : ℝ)^4243 ≤ (8782404832011/25000000000000 : ℝ)^3219 := by
    have hnat : (1130472551 : ℕ)^4243*25000000000000^3219 ≤ 8782404832011^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130472551 2500000000 8782404832011 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084817303/5000000000 : ℝ)^4243 ≤ (1972999288677/6250000000000 : ℝ)^3219 := by
    have hnat : (2084817303 : ℕ)^4243*6250000000000^3219 ≤ 1972999288677^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084817303 5000000000 1972999288677 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171153759/5000000000 : ℝ), (1130472551/2500000000 : ℝ), (2084817303/5000000000 : ℝ)] ![(6660478407919/20000000000000 : ℝ), (8782404832011/25000000000000 : ℝ), (1972999288677/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171153759/5000000000 : ℝ)|^4243 ≤ (6660478407919/20000000000000 : ℝ)^3219
        have hw : |(2171153759/5000000000 : ℝ)|=(2171153759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130472551/2500000000 : ℝ)|^4243 ≤ (8782404832011/25000000000000 : ℝ)^3219
        have hw : |(1130472551/2500000000 : ℝ)|=(1130472551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084817303/5000000000 : ℝ)|^4243 ≤ (1972999288677/6250000000000 : ℝ)^3219
        have hw : |(2084817303/5000000000 : ℝ)|=(2084817303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3667/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1099/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1099/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1099/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14681/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1099/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1099/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14681/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1099/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1099/10000 : ℝ) ^ (2121/512 : ℝ) ≤ (5323877121770187/50000000000000000000 : ℝ) := by
    have hpowers : (1099/10000 : ℝ)^2121 ≤ (5323877121770187/50000000000000000000 : ℝ)^512 := by
      have hnat : (1099 : ℕ)^2121*50000000000000000000^512 ≤ 5323877121770187^512*10000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1099 10000 5323877121770187 50000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1099/10000 : ℝ)) (X := (5323877121770187/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14681/100000 : ℝ) ^ (2121/512 : ℝ) ≤ (35336223728083849/100000000000000000000 : ℝ) := by
    have hpowers : (14681/100000 : ℝ)^2121 ≤ (35336223728083849/100000000000000000000 : ℝ)^512 := by
      have hnat : (14681 : ℕ)^2121*100000000000000000000^512 ≤ 35336223728083849^512*100000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14681 100000 35336223728083849 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14681/100000 : ℝ)) (X := (35336223728083849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005323877121770187/25000000000000000000 : ℝ) ≤ (312516063206843/312500000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (25005323877121770187/25000000000000000000 : ℝ)^512 ≤ (312516063206843/312500000000000 : ℝ)^2121 := by
      have hnat : (25005323877121770187 : ℕ)^512*312500000000000^2121 ≤ 312516063206843^2121*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005323877121770187 25000000000000000000 312516063206843 312500000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312516063206843/312500000000000 : ℝ)) (X := (25005323877121770187/25000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045983977971624223/100000000000000000000 : ℝ) ≤ (2000221967858183/2000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (100045983977971624223/100000000000000000000 : ℝ)^512 ≤ (2000221967858183/2000000000000000 : ℝ)^2121 := by
      have hnat : (100045983977971624223 : ℕ)^512*2000000000000000^2121 ≤ 2000221967858183^2121*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045983977971624223 100000000000000000000 2000221967858183 2000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221967858183/2000000000000000 : ℝ)) (X := (100045983977971624223/100000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035336223728083849/50000000000000000000 : ℝ) ≤ (5000852827981427/5000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50035336223728083849/50000000000000000000 : ℝ)^512 ≤ (5000852827981427/5000000000000000 : ℝ)^2121 := by
      have hnat : (50035336223728083849 : ℕ)^512*5000000000000000^2121 ≤ 5000852827981427^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035336223728083849 50000000000000000000 5000852827981427 5000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000852827981427/5000000000000000 : ℝ)) (X := (50035336223728083849/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5323877121770187/50000000000000000000 : ℝ) ≤ ((9224700301759355299/9227500000000000000 : ℝ)+2*(595816671939/369100000000000 : ℝ)*(1099/10000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (9224700301759355299/9227500000000000000 : ℝ)+2*(595816671939/369100000000000 : ℝ)*(1099/10000 : ℝ)=(312516063206843/312500000000000 : ℝ) by norm_num, show 1+2*(5323877121770187/50000000000000000000 : ℝ)=(25005323877121770187/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35336223728083849/100000000000000000000 : ℝ)+(5323877121770187/50000000000000000000 : ℝ) ≤ ((9224700301759355299/9227500000000000000 : ℝ)+(595816671939/369100000000000 : ℝ)*((14681/100000 : ℝ)+(1099/10000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (9224700301759355299/9227500000000000000 : ℝ)+(595816671939/369100000000000 : ℝ)*((14681/100000 : ℝ)+(1099/10000 : ℝ))=(2000221967858183/2000000000000000 : ℝ) by norm_num, show 1+(35336223728083849/100000000000000000000 : ℝ)+(5323877121770187/50000000000000000000 : ℝ)=(100045983977971624223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35336223728083849/100000000000000000000 : ℝ) ≤ ((9224700301759355299/9227500000000000000 : ℝ)+2*(595816671939/369100000000000 : ℝ)*(14681/100000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (9224700301759355299/9227500000000000000 : ℝ)+2*(595816671939/369100000000000 : ℝ)*(14681/100000 : ℝ)=(5000852827981427/5000000000000000 : ℝ) by norm_num, show 1+2*(35336223728083849/100000000000000000000 : ℝ)=(50035336223728083849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9224700301759355299/9227500000000000000 : ℝ)*(X 1 0+X 2 0)+(595816671939/369100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (9224700301759355299/9227500000000000000 : ℝ)) (alpha := (595816671939/369100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9224700301759355299/9227500000000000000 : ℝ)*(X 0 1+X 2 1)+(595816671939/369100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (9224700301759355299/9227500000000000000 : ℝ)) (alpha := (595816671939/369100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9224700301759355299/9227500000000000000 : ℝ)*(X 0 2+X 1 2)+(595816671939/369100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (14681/100000 : ℝ)) (c := (9224700301759355299/9227500000000000000 : ℝ)) (alpha := (595816671939/369100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-419210609/2000000000 : ℝ)*X 0 0+(216631717/400000000 : ℝ)*X 0 1+(655321123/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069987783/2000000000 : ℝ)*X 1 0+(-1092181559/5000000000 : ℝ)*X 1 1+(5242568973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069987781/2000000000 : ℝ)*X 2 0+(1310642243/2500000000 : ℝ)*X 2 1+(-1092181567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342281181/10000000000 : ℝ)*X 0 0+(4168362981/10000000000 : ℝ)*X 0 1+(1130788831/2500000000 : ℝ)*X 0 2+(4342281181/10000000000 : ℝ)*X 1 0+(4168362981/10000000000 : ℝ)*X 1 1+(1130788831/2500000000 : ℝ)*X 1 2+(4342281181/10000000000 : ℝ)*X 2 0+(4168362981/10000000000 : ℝ)*X 2 1+(1130788831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-524016477/2500000000 : ℝ)*X 0 0+(2621593331/5000000000 : ℝ)*X 0 1+(1353793017/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305640013/10000000000 : ℝ)*X 1 0+(-402352009/2000000000 : ℝ)*X 1 1+(2707586043/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652820023/5000000000 : ℝ)*X 2 0+(5415172057/10000000000 : ℝ)*X 2 1+(-2011760039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171153759/5000000000 : ℝ)*X 0 0+(1130472551/2500000000 : ℝ)*X 0 1+(2084817303/5000000000 : ℝ)*X 0 2+(2171153759/5000000000 : ℝ)*X 1 0+(1130472551/2500000000 : ℝ)*X 1 1+(2084817303/5000000000 : ℝ)*X 1 2+(2171153759/5000000000 : ℝ)*X 2 0+(1130472551/2500000000 : ℝ)*X 2 1+(2084817303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109946732442636717568287771/11534375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (932961913/50000000000000 : ℝ)*(base19) + (170833441/10000000000000 : ℝ)*(base23) + (19634107/25000000000000 : ℝ)*(lower2) + (259180539/100000000000000 : ℝ)*(upper3) + (1619687/1250000000000 : ℝ)*(upper5) + (419508601003/9765625000 : ℝ)*(major0) + (419508601003/9765625000 : ℝ)*(major1) + (419508601003/9765625000 : ℝ)*(major2) + (2886456497353271/50000000000000 : ℝ)*(sp0) + (5772947175045211/100000000000000 : ℝ)*(sp1) + (5772947332634627/100000000000000 : ℝ)*(sp2) + (1409283586127043/50000000000000 : ℝ)*(sp3) + (7209252499/20000000000000 : ℝ)*(sp4) + (9808790943/50000000000000 : ℝ)*(sp7) + (704646697458993/25000000000000 : ℝ)*(f.failure) + (5772949040969037/100000000000000 : ℝ)*(f.sum) + (325517684731/115343750000000000000000000 : ℝ)*base65 + (57107756602924717/5767187500000000000000000000000 : ℝ)*base68 + (147241410972727/1441796875000000000000000000000 : ℝ)*base69 + (84969741241596309/11534375000000000000000000000000 : ℝ)*base72 + (1431166086431/922750000000000000000000000 : ℝ)*base73 + (11161027673671309/11534375000000000000000000000000 : ℝ)*base76 + (37957674593690059/11534375000000000000000000000000 : ℝ)*base78 + (74537892354631533/5767187500000000000000000000000 : ℝ)*base79 + (6965519891837/1845500000000000000000000000 : ℝ)*base81 + (33900947/2500000000000000000000 : ℝ)*base89 + (33900947/2500000000000000000000 : ℝ)*base91 + (33900947/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1728827701694378502095847627/461375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (627736583/100000000000000 : ℝ)*(base19) + (744192239/100000000000000 : ℝ)*(base23) + (74124327/100000000000000 : ℝ)*(upper3) + (17874071/50000000000000 : ℝ)*(lower4) + (1626141/2000000000000 : ℝ)*(upper5) + (4326647163466909/100000000000000 : ℝ)*(major0) + (4326647163466909/100000000000000 : ℝ)*(major1) + (4326647163466909/100000000000000 : ℝ)*(major2) + (2597265981/20000000000000 : ℝ)*(sp1) + (7266482973/50000000000000 : ℝ)*(sp2) + (5814446683172667/100000000000000 : ℝ)*(sp4) + (2907216534553089/50000000000000 : ℝ)*(sp5) + (5814431406014481/100000000000000 : ℝ)*(sp6) + (283884751885713/10000000000000 : ℝ)*(sp7) + (283884751885713/10000000000000 : ℝ)*(f.failure) + (5814446683172667/100000000000000 : ℝ)*(f.sum) + (22796935844231/18455000000000000000000000000 : ℝ)*base65 + (2108495259059424209/922750000000000000000000000000000 : ℝ)*base68 + (4979069922730075791/922750000000000000000000000000000 : ℝ)*base69 + (5378943088039325791/922750000000000000000000000000000 : ℝ)*base71 + (128650072581049/18455000000000000000000000000 : ℝ)*base74 + (170324838418325791/922750000000000000000000000000000 : ℝ)*base75 + (4211681070265075791/922750000000000000000000000000000 : ℝ)*base77 + (3421953641840674209/922750000000000000000000000000000 : ℝ)*base80 + (1247657278923/2306875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1268173/1000000000000000000000 : ℝ)*base90 + (1268173/1000000000000000000000 : ℝ)*base92 + (1268173/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1283_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1283_s7_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048033563/5000000000 : ℝ)*x 0 + (676959797/1250000000 : ℝ)*x 1 + (1310668551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048033563/5000000000 : ℝ)^4243 ≤ (6375387266871/50000000000000 : ℝ)^3219 := by
    have hnat : (1048033563 : ℕ)^4243*50000000000000^3219 ≤ 6375387266871^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048033563 5000000000 6375387266871 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676959797/1250000000 : ℝ)^4243 ≤ (11139478579303/25000000000000 : ℝ)^3219 := by
    have hnat : (676959797 : ℕ)^4243*25000000000000^3219 ≤ 11139478579303^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676959797 1250000000 11139478579303 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310668551/2500000000 : ℝ)^4243 ≤ (1334103472871/3125000000000 : ℝ)^3219 := by
    have hnat : (1310668551 : ℕ)^4243*3125000000000^3219 ≤ 1334103472871^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310668551 2500000000 1334103472871 3125000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048033563/5000000000 : ℝ), (676959797/1250000000 : ℝ), (1310668551/2500000000 : ℝ)] ![(6375387266871/50000000000000 : ℝ), (11139478579303/25000000000000 : ℝ), (1334103472871/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048033563/5000000000 : ℝ)|^4243 ≤ (6375387266871/50000000000000 : ℝ)^3219
        have hw : |(-1048033563/5000000000 : ℝ)|=(1048033563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676959797/1250000000 : ℝ)|^4243 ≤ (11139478579303/25000000000000 : ℝ)^3219
        have hw : |(676959797/1250000000 : ℝ)|=(676959797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310668551/2500000000 : ℝ)|^4243 ≤ (1334103472871/3125000000000 : ℝ)^3219
        have hw : |(1310668551/2500000000 : ℝ)|=(1310668551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349910307/10000000000 : ℝ)*x 0 + (-273032783/1250000000 : ℝ)*x 1 + (655334263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349910307/10000000000 : ℝ)^4243 ≤ (1753842006801/4000000000000 : ℝ)^3219 := by
    have hnat : (5349910307 : ℕ)^4243*4000000000000^3219 ≤ 1753842006801^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349910307 10000000000 1753842006801 4000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273032783/1250000000 : ℝ)^4243 ≤ (13462639756639/100000000000000 : ℝ)^3219 := by
    have hnat : (273032783 : ℕ)^4243*100000000000000^3219 ≤ 13462639756639^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273032783 1250000000 13462639756639 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655334263/1250000000 : ℝ)^4243 ≤ (42691310058529/100000000000000 : ℝ)^3219 := by
    have hnat : (655334263 : ℕ)^4243*100000000000000^3219 ≤ 42691310058529^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655334263 1250000000 42691310058529 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349910307/10000000000 : ℝ), (-273032783/1250000000 : ℝ), (655334263/1250000000 : ℝ)] ![(1753842006801/4000000000000 : ℝ), (13462639756639/100000000000000 : ℝ), (42691310058529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349910307/10000000000 : ℝ)|^4243 ≤ (1753842006801/4000000000000 : ℝ)^3219
        have hw : |(5349910307/10000000000 : ℝ)|=(5349910307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273032783/1250000000 : ℝ)|^4243 ≤ (13462639756639/100000000000000 : ℝ)^3219
        have hw : |(-273032783/1250000000 : ℝ)|=(273032783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655334263/1250000000 : ℝ)|^4243 ≤ (42691310058529/100000000000000 : ℝ)^3219
        have hw : |(655334263/1250000000 : ℝ)|=(655334263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349909537/10000000000 : ℝ)*x 0 + (5242675383/10000000000 : ℝ)*x 1 + (-2184261599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349909537/10000000000 : ℝ)^4243 ≤ (70153666963/160000000000 : ℝ)^3219 := by
    have hnat : (5349909537 : ℕ)^4243*160000000000^3219 ≤ 70153666963^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349909537 10000000000 70153666963 160000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242675383/10000000000 : ℝ)^4243 ≤ (42691323786591/100000000000000 : ℝ)^3219 := by
    have hnat : (5242675383 : ℕ)^4243*100000000000000^3219 ≤ 42691323786591^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242675383 10000000000 42691323786591 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184261599/10000000000 : ℝ)^4243 ≤ (2692526870817/20000000000000 : ℝ)^3219 := by
    have hnat : (2184261599 : ℕ)^4243*20000000000000^3219 ≤ 2692526870817^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184261599 10000000000 2692526870817 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349909537/10000000000 : ℝ), (5242675383/10000000000 : ℝ), (-2184261599/10000000000 : ℝ)] ![(70153666963/160000000000 : ℝ), (42691323786591/100000000000000 : ℝ), (2692526870817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349909537/10000000000 : ℝ)|^4243 ≤ (70153666963/160000000000 : ℝ)^3219
        have hw : |(5349909537/10000000000 : ℝ)|=(5349909537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242675383/10000000000 : ℝ)|^4243 ≤ (42691323786591/100000000000000 : ℝ)^3219
        have hw : |(5242675383/10000000000 : ℝ)|=(5242675383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184261599/10000000000 : ℝ)|^4243 ≤ (2692526870817/20000000000000 : ℝ)^3219
        have hw : |(-2184261599/10000000000 : ℝ)|=(2184261599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342290419/10000000000 : ℝ)*x 0 + (521073313/1250000000 : ℝ)*x 1 + (4522928413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342290419/10000000000 : ℝ)^4243 ≤ (1332088767457/4000000000000 : ℝ)^3219 := by
    have hnat : (4342290419 : ℕ)^4243*4000000000000^3219 ≤ 1332088767457^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342290419 10000000000 1332088767457 4000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521073313/1250000000 : ℝ)^4243 ≤ (31557529691327/100000000000000 : ℝ)^3219 := by
    have hnat : (521073313 : ℕ)^4243*100000000000000^3219 ≤ 31557529691327^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521073313 1250000000 31557529691327 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522928413/10000000000 : ℝ)^4243 ≤ (35140251111777/100000000000000 : ℝ)^3219 := by
    have hnat : (4522928413 : ℕ)^4243*100000000000000^3219 ≤ 35140251111777^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522928413 10000000000 35140251111777 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342290419/10000000000 : ℝ), (521073313/1250000000 : ℝ), (4522928413/10000000000 : ℝ)] ![(1332088767457/4000000000000 : ℝ), (31557529691327/100000000000000 : ℝ), (35140251111777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342290419/10000000000 : ℝ)|^4243 ≤ (1332088767457/4000000000000 : ℝ)^3219
        have hw : |(4342290419/10000000000 : ℝ)|=(4342290419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521073313/1250000000 : ℝ)|^4243 ≤ (31557529691327/100000000000000 : ℝ)^3219
        have hw : |(521073313/1250000000 : ℝ)|=(521073313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522928413/10000000000 : ℝ)|^4243 ≤ (35140251111777/100000000000000 : ℝ)^3219
        have hw : |(4522928413/10000000000 : ℝ)|=(4522928413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096079923/10000000000 : ℝ)*x 0 + (2621645353/5000000000 : ℝ)*x 1 + (1353764681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096079923/10000000000 : ℝ)^4243 ≤ (6375438572147/50000000000000 : ℝ)^3219 := by
    have hnat : (2096079923 : ℕ)^4243*50000000000000^3219 ≤ 6375438572147^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096079923 10000000000 6375438572147 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621645353/5000000000 : ℝ)^4243 ≤ (42697928438977/100000000000000 : ℝ)^3219 := by
    have hnat : (2621645353 : ℕ)^4243*100000000000000^3219 ≤ 42697928438977^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621645353 5000000000 42697928438977 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353764681/2500000000 : ℝ)^4243 ≤ (22275597199431/50000000000000 : ℝ)^3219 := by
    have hnat : (1353764681 : ℕ)^4243*50000000000000^3219 ≤ 22275597199431^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353764681 2500000000 22275597199431 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096079923/10000000000 : ℝ), (2621645353/5000000000 : ℝ), (1353764681/2500000000 : ℝ)] ![(6375438572147/50000000000000 : ℝ), (42697928438977/100000000000000 : ℝ), (22275597199431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096079923/10000000000 : ℝ)|^4243 ≤ (6375438572147/50000000000000 : ℝ)^3219
        have hw : |(-2096079923/10000000000 : ℝ)|=(2096079923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621645353/5000000000 : ℝ)|^4243 ≤ (42697928438977/100000000000000 : ℝ)^3219
        have hw : |(2621645353/5000000000 : ℝ)|=(2621645353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353764681/2500000000 : ℝ)|^4243 ≤ (22275597199431/50000000000000 : ℝ)^3219
        have hw : |(1353764681/2500000000 : ℝ)|=(1353764681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_5 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305667157/10000000000 : ℝ)*x 0 + (-2011878443/10000000000 : ℝ)*x 1 + (5415058711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305667157/10000000000 : ℝ)^4243 ≤ (43368730472343/100000000000000 : ℝ)^3219 := by
    have hnat : (5305667157 : ℕ)^4243*100000000000000^3219 ≤ 43368730472343^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305667157 10000000000 43368730472343 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011878443/10000000000 : ℝ)^4243 ≤ (1208007526039/10000000000000 : ℝ)^3219 := by
    have hnat : (2011878443 : ℕ)^4243*10000000000000^3219 ≤ 1208007526039^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011878443 10000000000 1208007526039 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415058711/10000000000 : ℝ)^4243 ≤ (11137798564471/25000000000000 : ℝ)^3219 := by
    have hnat : (5415058711 : ℕ)^4243*25000000000000^3219 ≤ 11137798564471^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415058711 10000000000 11137798564471 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305667157/10000000000 : ℝ), (-2011878443/10000000000 : ℝ), (5415058711/10000000000 : ℝ)] ![(43368730472343/100000000000000 : ℝ), (1208007526039/10000000000000 : ℝ), (11137798564471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305667157/10000000000 : ℝ)|^4243 ≤ (43368730472343/100000000000000 : ℝ)^3219
        have hw : |(5305667157/10000000000 : ℝ)|=(5305667157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011878443/10000000000 : ℝ)|^4243 ≤ (1208007526039/10000000000000 : ℝ)^3219
        have hw : |(-2011878443/10000000000 : ℝ)|=(2011878443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415058711/10000000000 : ℝ)|^4243 ≤ (11137798564471/25000000000000 : ℝ)^3219
        have hw : |(5415058711/10000000000 : ℝ)|=(5415058711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_6 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663208389/1250000000 : ℝ)*x 0 + (1353764687/2500000000 : ℝ)*x 1 + (-2011878453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663208389/1250000000 : ℝ)^4243 ≤ (3469498399/8000000000 : ℝ)^3219 := by
    have hnat : (663208389 : ℕ)^4243*8000000000^3219 ≤ 3469498399^3219*1250000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663208389 1250000000 3469498399 8000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353764687/2500000000 : ℝ)^4243 ≤ (4455119465913/10000000000000 : ℝ)^3219 := by
    have hnat : (1353764687 : ℕ)^4243*10000000000000^3219 ≤ 4455119465913^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353764687 2500000000 4455119465913 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011878453/10000000000 : ℝ)^4243 ≤ (2416015067907/20000000000000 : ℝ)^3219 := by
    have hnat : (2011878453 : ℕ)^4243*20000000000000^3219 ≤ 2416015067907^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011878453 10000000000 2416015067907 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663208389/1250000000 : ℝ), (1353764687/2500000000 : ℝ), (-2011878453/10000000000 : ℝ)] ![(3469498399/8000000000 : ℝ), (4455119465913/10000000000000 : ℝ), (2416015067907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663208389/1250000000 : ℝ)|^4243 ≤ (3469498399/8000000000 : ℝ)^3219
        have hw : |(663208389/1250000000 : ℝ)|=(663208389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353764687/2500000000 : ℝ)|^4243 ≤ (4455119465913/10000000000000 : ℝ)^3219
        have hw : |(1353764687/2500000000 : ℝ)|=(1353764687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011878453/10000000000 : ℝ)|^4243 ≤ (2416015067907/20000000000000 : ℝ)^3219
        have hw : |(-2011878453/10000000000 : ℝ)|=(2011878453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_7 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085578807/2500000000 : ℝ)*x 0 + (4521666631/10000000000 : ℝ)*x 1 + (260616013/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085578807/2500000000 : ℝ)^4243 ≤ (260175546717/781250000000 : ℝ)^3219 := by
    have hnat : (1085578807 : ℕ)^4243*781250000000^3219 ≤ 260175546717^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085578807 2500000000 260175546717 781250000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521666631/10000000000 : ℝ)^4243 ≤ (35127329929381/100000000000000 : ℝ)^3219 := by
    have hnat : (4521666631 : ℕ)^4243*100000000000000^3219 ≤ 35127329929381^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521666631 10000000000 35127329929381 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260616013/625000000 : ℝ)^4243 ≤ (31570200074893/100000000000000 : ℝ)^3219 := by
    have hnat : (260616013 : ℕ)^4243*100000000000000^3219 ≤ 31570200074893^3219*625000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260616013 625000000 31570200074893 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085578807/2500000000 : ℝ), (4521666631/10000000000 : ℝ), (260616013/625000000 : ℝ)] ![(260175546717/781250000000 : ℝ), (35127329929381/100000000000000 : ℝ), (31570200074893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085578807/2500000000 : ℝ)|^4243 ≤ (260175546717/781250000000 : ℝ)^3219
        have hw : |(1085578807/2500000000 : ℝ)|=(1085578807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521666631/10000000000 : ℝ)|^4243 ≤ (35127329929381/100000000000000 : ℝ)^3219
        have hw : |(4521666631/10000000000 : ℝ)|=(4521666631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260616013/625000000 : ℝ)|^4243 ≤ (31570200074893/100000000000000 : ℝ)^3219
        have hw : |(260616013/625000000 : ℝ)|=(260616013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s7_8 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63503067/10000000000 : ℝ)*x 0 + (5904742359/10000000000 : ℝ)*x 1 + (5904755661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63503067/10000000000 : ℝ)^4243 ≤ (12701033289/10000000000000 : ℝ)^3219 := by
    have hnat : (63503067 : ℕ)^4243*10000000000000^3219 ≤ 12701033289^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63503067 10000000000 12701033289 10000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5904742359/10000000000 : ℝ)^4243 ≤ (6242052585893/12500000000000 : ℝ)^3219 := by
    have hnat : (5904742359 : ℕ)^4243*12500000000000^3219 ≤ 6242052585893^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904742359 10000000000 6242052585893 12500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5904755661/10000000000 : ℝ)^4243 ≤ (2496828448409/5000000000000 : ℝ)^3219 := by
    have hnat : (5904755661 : ℕ)^4243*5000000000000^3219 ≤ 2496828448409^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5904755661 10000000000 2496828448409 5000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63503067/10000000000 : ℝ), (5904742359/10000000000 : ℝ), (5904755661/10000000000 : ℝ)] ![(12701033289/10000000000000 : ℝ), (6242052585893/12500000000000 : ℝ), (2496828448409/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63503067/10000000000 : ℝ)|^4243 ≤ (12701033289/10000000000000 : ℝ)^3219
        have hw : |(-63503067/10000000000 : ℝ)|=(63503067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5904742359/10000000000 : ℝ)|^4243 ≤ (6242052585893/12500000000000 : ℝ)^3219
        have hw : |(5904742359/10000000000 : ℝ)|=(5904742359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5904755661/10000000000 : ℝ)|^4243 ≤ (2496828448409/5000000000000 : ℝ)^3219
        have hw : |(5904755661/10000000000 : ℝ)|=(5904755661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7333/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3667/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3667/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3667/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3667/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3667/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3667/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5501/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (2673999950499541/25000000000000000000 : ℝ) := by
    have hpowers : (5501/50000 : ℝ)^2121 ≤ (2673999950499541/25000000000000000000 : ℝ)^512 := by
      have hnat : (5501 : ℕ)^2121*25000000000000000000^512 ≤ 2673999950499541^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5501 50000 2673999950499541 25000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5501/50000 : ℝ)) (X := (2673999950499541/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3667/25000 : ℝ) ^ (2121/512 : ℝ) ≤ (35206782014678087/100000000000000000000 : ℝ) := by
    have hpowers : (3667/25000 : ℝ)^2121 ≤ (35206782014678087/100000000000000000000 : ℝ)^512 := by
      have hnat : (3667 : ℕ)^2121*100000000000000000000^512 ≤ 35206782014678087^512*25000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3667 25000 35206782014678087 100000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3667/25000 : ℝ)) (X := (35206782014678087/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502673999950499541/12500000000000000000 : ℝ) ≤ (2000103270298941/2000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (12502673999950499541/12500000000000000000 : ℝ)^512 ≤ (2000103270298941/2000000000000000 : ℝ)^2121 := by
      have hnat : (12502673999950499541 : ℕ)^512*2000000000000000^2121 ≤ 2000103270298941^2121*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502673999950499541 12500000000000000000 2000103270298941 2000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000103270298941/2000000000000000 : ℝ)) (X := (12502673999950499541/12500000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045902781816676251/100000000000000000000 : ℝ) ≤ (10001107879934573/10000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (100045902781816676251/100000000000000000000 : ℝ)^512 ≤ (10001107879934573/10000000000000000 : ℝ)^2121 := by
      have hnat : (100045902781816676251 : ℕ)^512*10000000000000000^2121 ≤ 10001107879934573^2121*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045902781816676251 100000000000000000000 10001107879934573 10000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001107879934573/10000000000000000 : ℝ)) (X := (100045902781816676251/100000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035206782014678087/50000000000000000000 : ℝ) ≤ (10001699408374441/10000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (50035206782014678087/50000000000000000000 : ℝ)^512 ≤ (10001699408374441/10000000000000000 : ℝ)^2121 := by
      have hnat : (50035206782014678087 : ℕ)^512*10000000000000000^2121 ≤ 10001699408374441^2121*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035206782014678087 50000000000000000000 10001699408374441 10000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001699408374441/10000000000000000 : ℝ)) (X := (50035206782014678087/50000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2673999950499541/25000000000000000000 : ℝ) ≤ ((18324438476394366529/18330000000000000000 : ℝ)+2*(147882109967/91650000000000 : ℝ)*(5501/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (18324438476394366529/18330000000000000000 : ℝ)+2*(147882109967/91650000000000 : ℝ)*(5501/50000 : ℝ)=(2000103270298941/2000000000000000 : ℝ) by norm_num, show 1+2*(2673999950499541/25000000000000000000 : ℝ)=(12502673999950499541/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35206782014678087/100000000000000000000 : ℝ)+(2673999950499541/25000000000000000000 : ℝ) ≤ ((18324438476394366529/18330000000000000000 : ℝ)+(147882109967/91650000000000 : ℝ)*((3667/25000 : ℝ)+(5501/50000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (18324438476394366529/18330000000000000000 : ℝ)+(147882109967/91650000000000 : ℝ)*((3667/25000 : ℝ)+(5501/50000 : ℝ))=(10001107879934573/10000000000000000 : ℝ) by norm_num, show 1+(35206782014678087/100000000000000000000 : ℝ)+(2673999950499541/25000000000000000000 : ℝ)=(100045902781816676251/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35206782014678087/100000000000000000000 : ℝ) ≤ ((18324438476394366529/18330000000000000000 : ℝ)+2*(147882109967/91650000000000 : ℝ)*(3667/25000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (18324438476394366529/18330000000000000000 : ℝ)+2*(147882109967/91650000000000 : ℝ)*(3667/25000 : ℝ)=(10001699408374441/10000000000000000 : ℝ) by norm_num, show 1+2*(35206782014678087/100000000000000000000 : ℝ)=(50035206782014678087/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18324438476394366529/18330000000000000000 : ℝ)*(X 1 0+X 2 0)+(147882109967/91650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (18324438476394366529/18330000000000000000 : ℝ)) (alpha := (147882109967/91650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18324438476394366529/18330000000000000000 : ℝ)*(X 0 1+X 2 1)+(147882109967/91650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (18324438476394366529/18330000000000000000 : ℝ)) (alpha := (147882109967/91650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18324438476394366529/18330000000000000000 : ℝ)*(X 0 2+X 1 2)+(147882109967/91650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (3667/25000 : ℝ)) (c := (18324438476394366529/18330000000000000000 : ℝ)) (alpha := (147882109967/91650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1048033563/5000000000 : ℝ)*X 0 0+(676959797/1250000000 : ℝ)*X 0 1+(1310668551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349910307/10000000000 : ℝ)*X 1 0+(-273032783/1250000000 : ℝ)*X 1 1+(655334263/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349909537/10000000000 : ℝ)*X 2 0+(5242675383/10000000000 : ℝ)*X 2 1+(-2184261599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342290419/10000000000 : ℝ)*X 0 0+(521073313/1250000000 : ℝ)*X 0 1+(4522928413/10000000000 : ℝ)*X 0 2+(4342290419/10000000000 : ℝ)*X 1 0+(521073313/1250000000 : ℝ)*X 1 1+(4522928413/10000000000 : ℝ)*X 1 2+(4342290419/10000000000 : ℝ)*X 2 0+(521073313/1250000000 : ℝ)*X 2 1+(4522928413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2096079923/10000000000 : ℝ)*X 0 0+(2621645353/5000000000 : ℝ)*X 0 1+(1353764681/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305667157/10000000000 : ℝ)*X 1 0+(-2011878443/10000000000 : ℝ)*X 1 1+(5415058711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663208389/1250000000 : ℝ)*X 2 0+(1353764687/2500000000 : ℝ)*X 2 1+(-2011878453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085578807/2500000000 : ℝ)*X 0 0+(4521666631/10000000000 : ℝ)*X 0 1+(260616013/625000000 : ℝ)*X 0 2+(1085578807/2500000000 : ℝ)*X 1 0+(4521666631/10000000000 : ℝ)*X 1 1+(260616013/625000000 : ℝ)*X 1 2+(1085578807/2500000000 : ℝ)*X 2 0+(4521666631/10000000000 : ℝ)*X 2 1+(260616013/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-63503067/10000000000 : ℝ)*X 0 0+(5904742359/10000000000 : ℝ)*X 0 1+(5904755661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2971502184383976982856141/1625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (651886677/100000000000000 : ℝ)*(lower2) + (477792579/100000000000000 : ℝ)*(lower3) + (202485093/20000000000000 : ℝ)*(lower4) + (2150600122036237/50000000000000 : ℝ)*(major0) + (2150600122036237/50000000000000 : ℝ)*(major1) + (2150600122036237/50000000000000 : ℝ)*(major2) + (5780223332161769/100000000000000 : ℝ)*(sp0) + (1156046062795733/20000000000000 : ℝ)*(sp1) + (2890124711056887/50000000000000 : ℝ)*(sp2) + (1411073982588911/50000000000000 : ℝ)*(sp3) + (9985588503/50000000000000 : ℝ)*(sp4) + (19108135109/100000000000000 : ℝ)*(sp5) + (3039899441/100000000000000 : ℝ)*(sp7) + (6118774999/100000000000000 : ℝ)*(sp8) + (1411075502538631/50000000000000 : ℝ)*(f.failure) + (2890124711056887/50000000000000 : ℝ)*(f.sum) + (28047822851449/9165000000000000000000000000 : ℝ)*base66 + (4260064372963711373/916500000000000000000000000000000 : ℝ)*base67 + (6256772387420788627/916500000000000000000000000000000 : ℝ)*base70 + (7332881144572711373/916500000000000000000000000000000 : ℝ)*base71 + (5111863584691/2291250000000000000000000000 : ℝ)*base74 + (11478374112429211373/916500000000000000000000000000000 : ℝ)*base75 + (87233216079967711373/916500000000000000000000000000000 : ℝ)*base77 + (8071211008617211373/916500000000000000000000000000000 : ℝ)*base79 + (2771603575913/1145625000000000000000000000 : ℝ)*base82 + (56684651/5000000000000000000000 : ℝ)*base90 + (56684651/5000000000000000000000 : ℝ)*base92 + (56684651/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (206026740857967783824746931/19093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52900907/100000000000000 : ℝ)*(upper1) + (280404319/50000000000000 : ℝ)*(lower2) + (52510401/25000000000000 : ℝ)*(lower3) + (587006799/100000000000000 : ℝ)*(lower4) + (195618163/100000000000000 : ℝ)*(lower5) + (541516135110011/12500000000000 : ℝ)*(major0) + (541516135110011/12500000000000 : ℝ)*(major1) + (541516135110011/12500000000000 : ℝ)*(major2) + (1743793711/100000000000000 : ℝ)*(sp3) + (2910904106045523/50000000000000 : ℝ)*(sp4) + (5821813427033829/100000000000000 : ℝ)*(sp5) + (5821813427033829/100000000000000 : ℝ)*(sp6) + (1421221315628457/50000000000000 : ℝ)*(sp7) + (5214942783/100000000000000 : ℝ)*(sp8) + (1421222187525313/50000000000000 : ℝ)*(f.failure) + (5821813427033829/100000000000000 : ℝ)*(f.sum) + (10809549516581/4582500000000000000000000000 : ℝ)*base65 + (3681231831838246819/229125000000000000000000000000000 : ℝ)*base67 + (9812207621232871819/229125000000000000000000000000000 : ℝ)*base69 + (3146930936100871819/229125000000000000000000000000000 : ℝ)*base71 + (31259685098077/9165000000000000000000000000 : ℝ)*base73 + (3400555878255871819/229125000000000000000000000000000 : ℝ)*base75 + (1821791609233996819/229125000000000000000000000000000 : ℝ)*base77 + (112922940327628181/229125000000000000000000000000000 : ℝ)*base80 + (60301970843111/4582500000000000000000000000 : ℝ)*base81 + (80860227/5000000000000000000000 : ℝ)*base89 + (80860227/5000000000000000000000 : ℝ)*base91 + (80860227/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1283_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3667/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1283_s8_0 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337476059/2500000000 : ℝ)*x 0 + (5242697217/10000000000 : ℝ)*x 1 + (-2184239801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337476059/2500000000 : ℝ)^4243 ≤ (10961496146571/25000000000000 : ℝ)^3219 := by
    have hnat : (1337476059 : ℕ)^4243*25000000000000^3219 ≤ 10961496146571^3219*2500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337476059 2500000000 10961496146571 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242697217/10000000000 : ℝ)^4243 ≤ (21345779070277/50000000000000 : ℝ)^3219 := by
    have hnat : (5242697217 : ℕ)^4243*50000000000000^3219 ≤ 21345779070277^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242697217 10000000000 21345779070277 50000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2184239801/10000000000 : ℝ)^4243 ≤ (673122863217/5000000000000 : ℝ)^3219 := by
    have hnat : (2184239801 : ℕ)^4243*5000000000000^3219 ≤ 673122863217^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184239801 10000000000 673122863217 5000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337476059/2500000000 : ℝ), (5242697217/10000000000 : ℝ), (-2184239801/10000000000 : ℝ)] ![(10961496146571/25000000000000 : ℝ), (21345779070277/50000000000000 : ℝ), (673122863217/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337476059/2500000000 : ℝ)|^4243 ≤ (10961496146571/25000000000000 : ℝ)^3219
        have hw : |(1337476059/2500000000 : ℝ)|=(1337476059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242697217/10000000000 : ℝ)|^4243 ≤ (21345779070277/50000000000000 : ℝ)^3219
        have hw : |(5242697217/10000000000 : ℝ)|=(5242697217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2184239801/10000000000 : ℝ)|^4243 ≤ (673122863217/5000000000000 : ℝ)^3219
        have hw : |(-2184239801/10000000000 : ℝ)|=(2184239801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s8_1 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096079257/10000000000 : ℝ)*x 0 + (5243312201/10000000000 : ℝ)*x 1 + (270751897/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096079257/10000000000 : ℝ)^4243 ≤ (12750871804083/100000000000000 : ℝ)^3219 := by
    have hnat : (2096079257 : ℕ)^4243*100000000000000^3219 ≤ 12750871804083^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096079257 10000000000 12750871804083 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243312201/10000000000 : ℝ)^4243 ≤ (8539631832583/20000000000000 : ℝ)^3219 := by
    have hnat : (5243312201 : ℕ)^4243*20000000000000^3219 ≤ 8539631832583^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243312201 10000000000 8539631832583 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270751897/500000000 : ℝ)^4243 ≤ (8910193801517/20000000000000 : ℝ)^3219 := by
    have hnat : (270751897 : ℕ)^4243*20000000000000^3219 ≤ 8910193801517^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270751897 500000000 8910193801517 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096079257/10000000000 : ℝ), (5243312201/10000000000 : ℝ), (270751897/500000000 : ℝ)] ![(12750871804083/100000000000000 : ℝ), (8539631832583/20000000000000 : ℝ), (8910193801517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096079257/10000000000 : ℝ)|^4243 ≤ (12750871804083/100000000000000 : ℝ)^3219
        have hw : |(-2096079257/10000000000 : ℝ)|=(2096079257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243312201/10000000000 : ℝ)|^4243 ≤ (8539631832583/20000000000000 : ℝ)^3219
        have hw : |(5243312201/10000000000 : ℝ)|=(5243312201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270751897/500000000 : ℝ)|^4243 ≤ (8910193801517/20000000000000 : ℝ)^3219
        have hw : |(270751897/500000000 : ℝ)|=(270751897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s8_2 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305673613/10000000000 : ℝ)*x 0 + (-2011898113/10000000000 : ℝ)*x 1 + (270751897/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305673613/10000000000 : ℝ)^4243 ≤ (43368800031189/100000000000000 : ℝ)^3219 := by
    have hnat : (5305673613 : ℕ)^4243*100000000000000^3219 ≤ 43368800031189^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305673613 10000000000 43368800031189 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011898113/10000000000 : ℝ)^4243 ≤ (755014433599/6250000000000 : ℝ)^3219 := by
    have hnat : (2011898113 : ℕ)^4243*6250000000000^3219 ≤ 755014433599^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011898113 10000000000 755014433599 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270751897/500000000 : ℝ)^4243 ≤ (8910193801517/20000000000000 : ℝ)^3219 := by
    have hnat : (270751897 : ℕ)^4243*20000000000000^3219 ≤ 8910193801517^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270751897 500000000 8910193801517 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305673613/10000000000 : ℝ), (-2011898113/10000000000 : ℝ), (270751897/500000000 : ℝ)] ![(43368800031189/100000000000000 : ℝ), (755014433599/6250000000000 : ℝ), (8910193801517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305673613/10000000000 : ℝ)|^4243 ≤ (43368800031189/100000000000000 : ℝ)^3219
        have hw : |(5305673613/10000000000 : ℝ)|=(5305673613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011898113/10000000000 : ℝ)|^4243 ≤ (755014433599/6250000000000 : ℝ)^3219
        have hw : |(-2011898113/10000000000 : ℝ)|=(2011898113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270751897/500000000 : ℝ)|^4243 ≤ (8910193801517/20000000000000 : ℝ)^3219
        have hw : |(270751897/500000000 : ℝ)|=(270751897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s8_3 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305673613/10000000000 : ℝ)*x 0 + (270751897/500000000 : ℝ)*x 1 + (-2011898113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305673613/10000000000 : ℝ)^4243 ≤ (43368800031189/100000000000000 : ℝ)^3219 := by
    have hnat : (5305673613 : ℕ)^4243*100000000000000^3219 ≤ 43368800031189^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305673613 10000000000 43368800031189 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270751897/500000000 : ℝ)^4243 ≤ (8910193801517/20000000000000 : ℝ)^3219 := by
    have hnat : (270751897 : ℕ)^4243*20000000000000^3219 ≤ 8910193801517^3219*500000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270751897 500000000 8910193801517 20000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011898113/10000000000 : ℝ)^4243 ≤ (755014433599/6250000000000 : ℝ)^3219 := by
    have hnat : (2011898113 : ℕ)^4243*6250000000000^3219 ≤ 755014433599^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011898113 10000000000 755014433599 6250000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305673613/10000000000 : ℝ), (270751897/500000000 : ℝ), (-2011898113/10000000000 : ℝ)] ![(43368800031189/100000000000000 : ℝ), (8910193801517/20000000000000 : ℝ), (755014433599/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305673613/10000000000 : ℝ)|^4243 ≤ (43368800031189/100000000000000 : ℝ)^3219
        have hw : |(5305673613/10000000000 : ℝ)|=(5305673613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270751897/500000000 : ℝ)|^4243 ≤ (8910193801517/20000000000000 : ℝ)^3219
        have hw : |(270751897/500000000 : ℝ)|=(270751897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011898113/10000000000 : ℝ)|^4243 ≤ (755014433599/6250000000000 : ℝ)^3219
        have hw : |(-2011898113/10000000000 : ℝ)|=(2011898113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1283_s8_4 (p : ℝ) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342316753/10000000000 : ℝ)*x 0 + (70650361/156250000 : ℝ)*x 1 + (2084949663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342316753/10000000000 : ℝ)^4243 ≤ (8325621348991/25000000000000 : ℝ)^3219 := by
    have hnat : (4342316753 : ℕ)^4243*25000000000000^3219 ≤ 8325621348991^3219*10000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342316753 10000000000 8325621348991 25000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70650361/156250000 : ℝ)^4243 ≤ (878172105373/2500000000000 : ℝ)^3219 := by
    have hnat : (70650361 : ℕ)^4243*2500000000000^3219 ≤ 878172105373^3219*156250000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70650361 156250000 878172105373 2500000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084949663/5000000000 : ℝ)^4243 ≤ (31570630371213/100000000000000 : ℝ)^3219 := by
    have hnat : (2084949663 : ℕ)^4243*100000000000000^3219 ≤ 31570630371213^3219*5000000000^4243 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084949663 5000000000 31570630371213 100000000000000 4243 3219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4243/1024 : ℝ)) 4243 3219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342316753/10000000000 : ℝ), (70650361/156250000 : ℝ), (2084949663/5000000000 : ℝ)] ![(8325621348991/25000000000000 : ℝ), (878172105373/2500000000000 : ℝ), (31570630371213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342316753/10000000000 : ℝ)|^4243 ≤ (8325621348991/25000000000000 : ℝ)^3219
        have hw : |(4342316753/10000000000 : ℝ)|=(4342316753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70650361/156250000 : ℝ)|^4243 ≤ (878172105373/2500000000000 : ℝ)^3219
        have hw : |(70650361/156250000 : ℝ)|=(70650361/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2084949663/5000000000 : ℝ)|^4243 ≤ (31570630371213/100000000000000 : ℝ)^3219
        have hw : |(2084949663/5000000000 : ℝ)|=(2084949663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1283_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2933/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/20000 : ℝ) ^ (2121/512 : ℝ) ≤ (2677021764915717/25000000000000000000 : ℝ) := by
    have hpowers : (2201/20000 : ℝ)^2121 ≤ (2677021764915717/25000000000000000000 : ℝ)^512 := by
      have hnat : (2201 : ℕ)^2121*25000000000000000000^512 ≤ 2677021764915717^512*20000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 20000 2677021764915717 25000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/20000 : ℝ)) (X := (2677021764915717/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7333/50000 : ℝ) ^ (2121/512 : ℝ) ≤ (7037379975316629/20000000000000000000 : ℝ) := by
    have hpowers : (7333/50000 : ℝ)^2121 ≤ (7037379975316629/20000000000000000000 : ℝ)^512 := by
      have hnat : (7333 : ℕ)^2121*20000000000000000000^512 ≤ 7037379975316629^512*50000^2121 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7333 50000 7037379975316629 20000000000000000000 2121 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7333/50000 : ℝ)) (X := (7037379975316629/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502677021764915717/12500000000000000000 : ℝ) ≤ (2000103386992411/2000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (12502677021764915717/12500000000000000000 : ℝ)^512 ≤ (2000103386992411/2000000000000000 : ℝ)^2121 := by
      have hnat : (12502677021764915717 : ℕ)^512*2000000000000000^2121 ≤ 2000103386992411^2121*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502677021764915717 12500000000000000000 2000103386992411 2000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000103386992411/2000000000000000 : ℝ)) (X := (12502677021764915717/12500000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045894986936246013/100000000000000000000 : ℝ) ≤ (2000221538367021/2000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (100045894986936246013/100000000000000000000 : ℝ)^512 ≤ (2000221538367021/2000000000000000 : ℝ)^2121 := by
      have hnat : (100045894986936246013 : ℕ)^512*2000000000000000^2121 ≤ 2000221538367021^2121*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045894986936246013 100000000000000000000 2000221538367021 2000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221538367021/2000000000000000 : ℝ)) (X := (100045894986936246013/100000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007037379975316629/10000000000000000000 : ℝ) ≤ (2000339689741631/2000000000000000 : ℝ) ^ (2121/512 : ℝ) := by
    have hpowers : (10007037379975316629/10000000000000000000 : ℝ)^512 ≤ (2000339689741631/2000000000000000 : ℝ)^2121 := by
      have hnat : (10007037379975316629 : ℕ)^512*2000000000000000^2121 ≤ 2000339689741631^2121*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007037379975316629 10000000000000000000 2000339689741631 2000000000000000 512 2121 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000339689741631/2000000000000000 : ℝ)) (X := (10007037379975316629/10000000000000000000 : ℝ)) (by norm_num) 2121 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2677021764915717/25000000000000000000 : ℝ) ≤ ((7319777988024050571/7322000000000000000 : ℝ)+2*(11815137461/7322000000000 : ℝ)*(2201/20000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (7319777988024050571/7322000000000000000 : ℝ)+2*(11815137461/7322000000000 : ℝ)*(2201/20000 : ℝ)=(2000103386992411/2000000000000000 : ℝ) by norm_num, show 1+2*(2677021764915717/25000000000000000000 : ℝ)=(12502677021764915717/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7037379975316629/20000000000000000000 : ℝ)+(2677021764915717/25000000000000000000 : ℝ) ≤ ((7319777988024050571/7322000000000000000 : ℝ)+(11815137461/7322000000000 : ℝ)*((7333/50000 : ℝ)+(2201/20000 : ℝ)))^(2121/512 : ℝ) := by
    rw [show (7319777988024050571/7322000000000000000 : ℝ)+(11815137461/7322000000000 : ℝ)*((7333/50000 : ℝ)+(2201/20000 : ℝ))=(2000221538367021/2000000000000000 : ℝ) by norm_num, show 1+(7037379975316629/20000000000000000000 : ℝ)+(2677021764915717/25000000000000000000 : ℝ)=(100045894986936246013/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7037379975316629/20000000000000000000 : ℝ) ≤ ((7319777988024050571/7322000000000000000 : ℝ)+2*(11815137461/7322000000000 : ℝ)*(7333/50000 : ℝ))^(2121/512 : ℝ) := by
    rw [show (7319777988024050571/7322000000000000000 : ℝ)+2*(11815137461/7322000000000 : ℝ)*(7333/50000 : ℝ)=(2000339689741631/2000000000000000 : ℝ) by norm_num, show 1+2*(7037379975316629/20000000000000000000 : ℝ)=(10007037379975316629/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7319777988024050571/7322000000000000000 : ℝ)*(X 1 0+X 2 0)+(11815137461/7322000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (7319777988024050571/7322000000000000000 : ℝ)) (alpha := (11815137461/7322000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7319777988024050571/7322000000000000000 : ℝ)*(X 0 1+X 2 1)+(11815137461/7322000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (7319777988024050571/7322000000000000000 : ℝ)) (alpha := (11815137461/7322000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7319777988024050571/7322000000000000000 : ℝ)*(X 0 2+X 1 2)+(11815137461/7322000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2121/512 : ℝ)) (lo := (2201/20000 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (7319777988024050571/7322000000000000000 : ℝ)) (alpha := (11815137461/7322000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1337476059/2500000000 : ℝ)*X 2 0+(5242697217/10000000000 : ℝ)*X 2 1+(-2184239801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2096079257/10000000000 : ℝ)*X 0 0+(5243312201/10000000000 : ℝ)*X 0 1+(270751897/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305673613/10000000000 : ℝ)*X 1 0+(-2011898113/10000000000 : ℝ)*X 1 1+(270751897/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305673613/10000000000 : ℝ)*X 2 0+(270751897/500000000 : ℝ)*X 2 1+(-2011898113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4342316753/10000000000 : ℝ)*X 0 0+(70650361/156250000 : ℝ)*X 0 1+(2084949663/5000000000 : ℝ)*X 0 2+(4342316753/10000000000 : ℝ)*X 1 0+(70650361/156250000 : ℝ)*X 1 1+(2084949663/5000000000 : ℝ)*X 1 2+(4342316753/10000000000 : ℝ)*X 2 0+(70650361/156250000 : ℝ)*X 2 1+(2084949663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1283_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50561550419453810737852959/22881250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199228377/50000000000000 : ℝ)*(base19) + (86661593/20000000000000 : ℝ)*(base23) + (137275253/100000000000000 : ℝ)*(lower1) + (22707829/50000000000000 : ℝ)*(upper3) + (15814127/100000000000000 : ℝ)*(lower4) + (5734189/12500000000000 : ℝ)*(upper5) + (270823962947393/6250000000000 : ℝ)*(major0) + (270823962947393/6250000000000 : ℝ)*(major1) + (270823962947393/6250000000000 : ℝ)*(major2) + (15129729/2500000000000 : ℝ)*(sp0) + (2911615294703387/50000000000000 : ℝ)*(sp1) + (5823230190950019/100000000000000 : ℝ)*(sp2) + (363951846931853/6250000000000 : ℝ)*(sp3) + (568627230250377/20000000000000 : ℝ)*(sp4) + (568627230250377/20000000000000 : ℝ)*(f.failure) + (2911615294703387/50000000000000 : ℝ)*(f.sum) + (13092598877227/3661000000000000000000000000 : ℝ)*base66 + (323245824780563597/45762500000000000000000000000000 : ℝ)*base68 + (758082676573263597/45762500000000000000000000000000 : ℝ)*base70 + (678404807712961403/45762500000000000000000000000000 : ℝ)*base71 + (11608042897593/3661000000000000000000000000 : ℝ)*base74 + (36211972989513597/45762500000000000000000000000000 : ℝ)*base76 + (83682160903498903/45762500000000000000000000000000 : ℝ)*base77 + (362435148740888597/45762500000000000000000000000000 : ℝ)*base80 + (9155925475803/1830500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12784283/2000000000000000000000 : ℝ)*base89 + (12784283/2000000000000000000000 : ℝ)*base91 + (12784283/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1283_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1283_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1283_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1283_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1283_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1283_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2121/512 : ℝ) ≤ p) (hpb : p ≤ (4243/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152408579/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14681/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1283_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
