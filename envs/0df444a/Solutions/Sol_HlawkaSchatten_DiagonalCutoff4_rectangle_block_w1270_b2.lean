-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1270_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:11.947986+00:00
-- url     : https://prove2.me/submissions/fdd6353f-9777-4dfb-bf24-7a6c8be129ec

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
theorem support_rectangle_w1270_s6_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106669677/10000000000 : ℝ)*x 0 + (5390814859/10000000000 : ℝ)*x 1 + (1316859859/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106669677/10000000000 : ℝ)^529 ≤ (2562813926747/20000000000000 : ℝ)^401 := by
    have hnat : (2106669677 : ℕ)^529*20000000000000^401 ≤ 2562813926747^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106669677 10000000000 2562813926747 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390814859/10000000000 : ℝ)^529 ≤ (11064657621757/25000000000000 : ℝ)^401 := by
    have hnat : (5390814859 : ℕ)^529*25000000000000^401 ≤ 11064657621757^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390814859 10000000000 11064657621757 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316859859/2500000000 : ℝ)^529 ≤ (21463649930793/50000000000000 : ℝ)^401 := by
    have hnat : (1316859859 : ℕ)^529*50000000000000^401 ≤ 21463649930793^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316859859 2500000000 21463649930793 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106669677/10000000000 : ℝ), (5390814859/10000000000 : ℝ), (1316859859/2500000000 : ℝ)] ![(2562813926747/20000000000000 : ℝ), (11064657621757/25000000000000 : ℝ), (21463649930793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106669677/10000000000 : ℝ)|^529 ≤ (2562813926747/20000000000000 : ℝ)^401
        have hw : |(-2106669677/10000000000 : ℝ)|=(2106669677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390814859/10000000000 : ℝ)|^529 ≤ (11064657621757/25000000000000 : ℝ)^401
        have hw : |(5390814859/10000000000 : ℝ)|=(5390814859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316859859/2500000000 : ℝ)|^529 ≤ (21463649930793/50000000000000 : ℝ)^401
        have hw : |(1316859859/2500000000 : ℝ)|=(1316859859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344190193/10000000000 : ℝ)*x 0 + (-2169219789/10000000000 : ℝ)*x 1 + (526743943/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344190193/10000000000 : ℝ)^529 ≤ (43754353090619/100000000000000 : ℝ)^401 := by
    have hnat : (5344190193 : ℕ)^529*100000000000000^401 ≤ 43754353090619^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344190193 10000000000 43754353090619 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169219789/10000000000 : ℝ)^529 ≤ (13318347100833/100000000000000 : ℝ)^401 := by
    have hnat : (2169219789 : ℕ)^529*100000000000000^401 ≤ 13318347100833^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169219789 10000000000 13318347100833 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526743943/1000000000 : ℝ)^529 ≤ (1073182494927/2500000000000 : ℝ)^401 := by
    have hnat : (526743943 : ℕ)^529*2500000000000^401 ≤ 1073182494927^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526743943 1000000000 1073182494927 2500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344190193/10000000000 : ℝ), (-2169219789/10000000000 : ℝ), (526743943/1000000000 : ℝ)] ![(43754353090619/100000000000000 : ℝ), (13318347100833/100000000000000 : ℝ), (1073182494927/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344190193/10000000000 : ℝ)|^529 ≤ (43754353090619/100000000000000 : ℝ)^401
        have hw : |(5344190193/10000000000 : ℝ)|=(5344190193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169219789/10000000000 : ℝ)|^529 ≤ (13318347100833/100000000000000 : ℝ)^401
        have hw : |(-2169219789/10000000000 : ℝ)|=(2169219789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526743943/1000000000 : ℝ)|^529 ≤ (1073182494927/2500000000000 : ℝ)^401
        have hw : |(526743943/1000000000 : ℝ)|=(526743943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672095099/5000000000 : ℝ)*x 0 + (5267439429/10000000000 : ℝ)*x 1 + (-2169219783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672095099/5000000000 : ℝ)^529 ≤ (21877176572311/50000000000000 : ℝ)^401 := by
    have hnat : (2672095099 : ℕ)^529*50000000000000^401 ≤ 21877176572311^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672095099 5000000000 21877176572311 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267439429/10000000000 : ℝ)^529 ≤ (42927299786329/100000000000000 : ℝ)^401 := by
    have hnat : (5267439429 : ℕ)^529*100000000000000^401 ≤ 42927299786329^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267439429 10000000000 42927299786329 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2169219783/10000000000 : ℝ)^529 ≤ (3329586763059/25000000000000 : ℝ)^401 := by
    have hnat : (2169219783 : ℕ)^529*25000000000000^401 ≤ 3329586763059^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169219783 10000000000 3329586763059 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672095099/5000000000 : ℝ), (5267439429/10000000000 : ℝ), (-2169219783/10000000000 : ℝ)] ![(21877176572311/50000000000000 : ℝ), (42927299786329/100000000000000 : ℝ), (3329586763059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672095099/5000000000 : ℝ)|^529 ≤ (21877176572311/50000000000000 : ℝ)^401
        have hw : |(2672095099/5000000000 : ℝ)|=(2672095099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267439429/10000000000 : ℝ)|^529 ≤ (42927299786329/100000000000000 : ℝ)^401
        have hw : |(5267439429/10000000000 : ℝ)|=(5267439429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2169219783/10000000000 : ℝ)|^529 ≤ (3329586763059/25000000000000 : ℝ)^401
        have hw : |(-2169219783/10000000000 : ℝ)|=(2169219783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (434680329/1000000000 : ℝ)*x 0 + (2111361763/5000000000 : ℝ)*x 1 + (4474401471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434680329/1000000000 : ℝ)^529 ≤ (33317555138441/100000000000000 : ℝ)^401 := by
    have hnat : (434680329 : ℕ)^529*100000000000000^401 ≤ 33317555138441^401*1000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434680329 1000000000 33317555138441 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111361763/5000000000 : ℝ)^529 ≤ (32068679265771/100000000000000 : ℝ)^401 := by
    have hnat : (2111361763 : ℕ)^529*100000000000000^401 ≤ 32068679265771^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111361763 5000000000 32068679265771 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474401471/10000000000 : ℝ)^529 ≤ (34613765575897/100000000000000 : ℝ)^401 := by
    have hnat : (4474401471 : ℕ)^529*100000000000000^401 ≤ 34613765575897^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474401471 10000000000 34613765575897 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434680329/1000000000 : ℝ), (2111361763/5000000000 : ℝ), (4474401471/10000000000 : ℝ)] ![(33317555138441/100000000000000 : ℝ), (32068679265771/100000000000000 : ℝ), (34613765575897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434680329/1000000000 : ℝ)|^529 ≤ (33317555138441/100000000000000 : ℝ)^401
        have hw : |(434680329/1000000000 : ℝ)|=(434680329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111361763/5000000000 : ℝ)|^529 ≤ (32068679265771/100000000000000 : ℝ)^401
        have hw : |(2111361763/5000000000 : ℝ)|=(2111361763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474401471/10000000000 : ℝ)|^529 ≤ (34613765575897/100000000000000 : ℝ)^401
        have hw : |(4474401471/10000000000 : ℝ)|=(4474401471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053337113/5000000000 : ℝ)*x 0 + (658468981/1250000000 : ℝ)*x 1 + (5390501371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053337113/5000000000 : ℝ)^529 ≤ (12814106135849/100000000000000 : ℝ)^401 := by
    have hnat : (1053337113 : ℕ)^529*100000000000000^401 ≤ 12814106135849^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053337113 5000000000 12814106135849 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658468981/1250000000 : ℝ)^529 ≤ (10732664651851/25000000000000 : ℝ)^401 := by
    have hnat : (658468981 : ℕ)^529*25000000000000^401 ≤ 10732664651851^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658468981 1250000000 10732664651851 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390501371/10000000000 : ℝ)^529 ≤ (8851047047427/20000000000000 : ℝ)^401 := by
    have hnat : (5390501371 : ℕ)^529*20000000000000^401 ≤ 8851047047427^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390501371 10000000000 8851047047427 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053337113/5000000000 : ℝ), (658468981/1250000000 : ℝ), (5390501371/10000000000 : ℝ)] ![(12814106135849/100000000000000 : ℝ), (10732664651851/25000000000000 : ℝ), (8851047047427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053337113/5000000000 : ℝ)|^529 ≤ (12814106135849/100000000000000 : ℝ)^401
        have hw : |(-1053337113/5000000000 : ℝ)|=(1053337113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658468981/1250000000 : ℝ)|^529 ≤ (10732664651851/25000000000000 : ℝ)^401
        have hw : |(658468981/1250000000 : ℝ)|=(658468981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390501371/10000000000 : ℝ)|^529 ≤ (8851047047427/20000000000000 : ℝ)^401
        have hw : |(5390501371/10000000000 : ℝ)|=(5390501371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312649441/10000000000 : ℝ)*x 0 + (-511539449/2500000000 : ℝ)*x 1 + (1078100291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312649441/10000000000 : ℝ)^529 ≤ (43414013180189/100000000000000 : ℝ)^401 := by
    have hnat : (5312649441 : ℕ)^529*100000000000000^401 ≤ 43414013180189^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312649441 10000000000 43414013180189 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511539449/2500000000 : ℝ)^529 ≤ (1233075065917/10000000000000 : ℝ)^401 := by
    have hnat : (511539449 : ℕ)^529*10000000000000^401 ≤ 1233075065917^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511539449 2500000000 1233075065917 10000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078100291/2000000000 : ℝ)^529 ≤ (44255236146893/100000000000000 : ℝ)^401 := by
    have hnat : (1078100291 : ℕ)^529*100000000000000^401 ≤ 44255236146893^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078100291 2000000000 44255236146893 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312649441/10000000000 : ℝ), (-511539449/2500000000 : ℝ), (1078100291/2000000000 : ℝ)] ![(43414013180189/100000000000000 : ℝ), (1233075065917/10000000000000 : ℝ), (44255236146893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312649441/10000000000 : ℝ)|^529 ≤ (43414013180189/100000000000000 : ℝ)^401
        have hw : |(5312649441/10000000000 : ℝ)|=(5312649441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-511539449/2500000000 : ℝ)|^529 ≤ (1233075065917/10000000000000 : ℝ)^401
        have hw : |(-511539449/2500000000 : ℝ)|=(511539449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078100291/2000000000 : ℝ)|^529 ≤ (44255236146893/100000000000000 : ℝ)^401
        have hw : |(1078100291/2000000000 : ℝ)|=(1078100291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312649649/10000000000 : ℝ)*x 0 + (1347625361/2500000000 : ℝ)*x 1 + (-255769691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312649649/10000000000 : ℝ)^529 ≤ (43414015422487/100000000000000 : ℝ)^401 := by
    have hnat : (5312649649 : ℕ)^529*100000000000000^401 ≤ 43414015422487^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312649649 10000000000 43414015422487 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347625361/2500000000 : ℝ)^529 ≤ (22127618013879/50000000000000 : ℝ)^401 := by
    have hnat : (1347625361 : ℕ)^529*50000000000000^401 ≤ 22127618013879^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347625361 2500000000 22127618013879 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (255769691/1250000000 : ℝ)^529 ≤ (12330748528597/100000000000000 : ℝ)^401 := by
    have hnat : (255769691 : ℕ)^529*100000000000000^401 ≤ 12330748528597^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255769691 1250000000 12330748528597 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312649649/10000000000 : ℝ), (1347625361/2500000000 : ℝ), (-255769691/1250000000 : ℝ)] ![(43414015422487/100000000000000 : ℝ), (22127618013879/50000000000000 : ℝ), (12330748528597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312649649/10000000000 : ℝ)|^529 ≤ (43414015422487/100000000000000 : ℝ)^401
        have hw : |(5312649649/10000000000 : ℝ)|=(5312649649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347625361/2500000000 : ℝ)|^529 ≤ (22127618013879/50000000000000 : ℝ)^401
        have hw : |(1347625361/2500000000 : ℝ)|=(1347625361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-255769691/1250000000 : ℝ)|^529 ≤ (12330748528597/100000000000000 : ℝ)^401
        have hw : |(-255769691/1250000000 : ℝ)|=(255769691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s6_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346812737/10000000000 : ℝ)*x 0 + (4473764477/10000000000 : ℝ)*x 1 + (1055840709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346812737/10000000000 : ℝ)^529 ≤ (16658825330781/50000000000000 : ℝ)^401 := by
    have hnat : (4346812737 : ℕ)^529*50000000000000^401 ≤ 16658825330781^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346812737 10000000000 16658825330781 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473764477/10000000000 : ℝ)^529 ≤ (6921453003477/20000000000000 : ℝ)^401 := by
    have hnat : (4473764477 : ℕ)^529*20000000000000^401 ≤ 6921453003477^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473764477 10000000000 6921453003477 20000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055840709/2500000000 : ℝ)^529 ≤ (32075084303861/100000000000000 : ℝ)^401 := by
    have hnat : (1055840709 : ℕ)^529*100000000000000^401 ≤ 32075084303861^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055840709 2500000000 32075084303861 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346812737/10000000000 : ℝ), (4473764477/10000000000 : ℝ), (1055840709/2500000000 : ℝ)] ![(16658825330781/50000000000000 : ℝ), (6921453003477/20000000000000 : ℝ), (32075084303861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346812737/10000000000 : ℝ)|^529 ≤ (16658825330781/50000000000000 : ℝ)^401
        have hw : |(4346812737/10000000000 : ℝ)|=(4346812737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473764477/10000000000 : ℝ)|^529 ≤ (6921453003477/20000000000000 : ℝ)^401
        have hw : |(4473764477/10000000000 : ℝ)|=(4473764477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055840709/2500000000 : ℝ)|^529 ≤ (32075084303861/100000000000000 : ℝ)^401
        have hw : |(1055840709/2500000000 : ℝ)|=(1055840709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11509/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14123/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7071/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7071/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7071/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7071/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7071/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7071/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11491/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (13094649606477929/100000000000000000000 : ℝ) := by
    have hpowers : (11491/100000 : ℝ)^8463 ≤ (13094649606477929/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11491 : ℕ)^8463*100000000000000000000^2048 ≤ 13094649606477929^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11491 100000 13094649606477929 100000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11491/100000 : ℝ)) (X := (13094649606477929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7071/50000 : ℝ) ^ (8463/2048 : ℝ) ≤ (3859627163721289/12500000000000000000 : ℝ) := by
    have hpowers : (7071/50000 : ℝ)^8463 ≤ (3859627163721289/12500000000000000000 : ℝ)^2048 := by
      have hnat : (7071 : ℕ)^8463*12500000000000000000^2048 ≤ 3859627163721289^2048*50000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7071 50000 3859627163721289 12500000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7071/50000 : ℝ)) (X := (3859627163721289/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013094649606477929/50000000000000000000 : ℝ) ≤ (5000316851954543/5000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50013094649606477929/50000000000000000000 : ℝ)^2048 ≤ (5000316851954543/5000000000000000 : ℝ)^8463 := by
      have hnat : (50013094649606477929 : ℕ)^2048*5000000000000000^8463 ≤ 5000316851954543^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013094649606477929 50000000000000000000 5000316851954543 5000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000316851954543/5000000000000000 : ℝ)) (X := (50013094649606477929/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043971666916248241/100000000000000000000 : ℝ) ≤ (10001063913149857/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (100043971666916248241/100000000000000000000 : ℝ)^2048 ≤ (10001063913149857/10000000000000000 : ℝ)^8463 := by
      have hnat : (100043971666916248241 : ℕ)^2048*10000000000000000^8463 ≤ 10001063913149857^8463*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043971666916248241 100000000000000000000 10001063913149857 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001063913149857/10000000000000000 : ℝ)) (X := (100043971666916248241/100000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253859627163721289/6250000000000000000 : ℝ) ≤ (2500373530597657/2500000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (6253859627163721289/6250000000000000000 : ℝ)^2048 ≤ (2500373530597657/2500000000000000 : ℝ)^8463 := by
      have hnat : (6253859627163721289 : ℕ)^2048*2500000000000000^8463 ≤ 2500373530597657^8463*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253859627163721289 6250000000000000000 2500373530597657 2500000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500373530597657/2500000000000000 : ℝ)) (X := (6253859627163721289/6250000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13094649606477929/100000000000000000000 : ℝ) ≤ ((3312724110036448483/3313750000000000000 : ℝ)+2*(430209240771/265100000000000 : ℝ)*(11491/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (3312724110036448483/3313750000000000000 : ℝ)+2*(430209240771/265100000000000 : ℝ)*(11491/100000 : ℝ)=(5000316851954543/5000000000000000 : ℝ) by norm_num, show 1+2*(13094649606477929/100000000000000000000 : ℝ)=(50013094649606477929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3859627163721289/12500000000000000000 : ℝ)+(13094649606477929/100000000000000000000 : ℝ) ≤ ((3312724110036448483/3313750000000000000 : ℝ)+(430209240771/265100000000000 : ℝ)*((7071/50000 : ℝ)+(11491/100000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (3312724110036448483/3313750000000000000 : ℝ)+(430209240771/265100000000000 : ℝ)*((7071/50000 : ℝ)+(11491/100000 : ℝ))=(10001063913149857/10000000000000000 : ℝ) by norm_num, show 1+(3859627163721289/12500000000000000000 : ℝ)+(13094649606477929/100000000000000000000 : ℝ)=(100043971666916248241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3859627163721289/12500000000000000000 : ℝ) ≤ ((3312724110036448483/3313750000000000000 : ℝ)+2*(430209240771/265100000000000 : ℝ)*(7071/50000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (3312724110036448483/3313750000000000000 : ℝ)+2*(430209240771/265100000000000 : ℝ)*(7071/50000 : ℝ)=(2500373530597657/2500000000000000 : ℝ) by norm_num, show 1+2*(3859627163721289/12500000000000000000 : ℝ)=(6253859627163721289/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3312724110036448483/3313750000000000000 : ℝ)*(X 1 0+X 2 0)+(430209240771/265100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11491/100000 : ℝ)) (hi := (7071/50000 : ℝ)) (c := (3312724110036448483/3313750000000000000 : ℝ)) (alpha := (430209240771/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3312724110036448483/3313750000000000000 : ℝ)*(X 0 1+X 2 1)+(430209240771/265100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11491/100000 : ℝ)) (hi := (7071/50000 : ℝ)) (c := (3312724110036448483/3313750000000000000 : ℝ)) (alpha := (430209240771/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3312724110036448483/3313750000000000000 : ℝ)*(X 0 2+X 1 2)+(430209240771/265100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11491/100000 : ℝ)) (hi := (7071/50000 : ℝ)) (c := (3312724110036448483/3313750000000000000 : ℝ)) (alpha := (430209240771/265100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2106669677/10000000000 : ℝ)*X 0 0+(5390814859/10000000000 : ℝ)*X 0 1+(1316859859/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344190193/10000000000 : ℝ)*X 1 0+(-2169219789/10000000000 : ℝ)*X 1 1+(526743943/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672095099/5000000000 : ℝ)*X 2 0+(5267439429/10000000000 : ℝ)*X 2 1+(-2169219783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((434680329/1000000000 : ℝ)*X 0 0+(2111361763/5000000000 : ℝ)*X 0 1+(4474401471/10000000000 : ℝ)*X 0 2+(434680329/1000000000 : ℝ)*X 1 0+(2111361763/5000000000 : ℝ)*X 1 1+(4474401471/10000000000 : ℝ)*X 1 2+(434680329/1000000000 : ℝ)*X 2 0+(2111361763/5000000000 : ℝ)*X 2 1+(4474401471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1053337113/5000000000 : ℝ)*X 0 0+(658468981/1250000000 : ℝ)*X 0 1+(5390501371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312649441/10000000000 : ℝ)*X 1 0+(-511539449/2500000000 : ℝ)*X 1 1+(1078100291/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312649649/10000000000 : ℝ)*X 2 0+(1347625361/2500000000 : ℝ)*X 2 1+(-255769691/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346812737/10000000000 : ℝ)*X 0 0+(4473764477/10000000000 : ℝ)*X 0 1+(1055840709/2500000000 : ℝ)*X 0 2+(4346812737/10000000000 : ℝ)*X 1 0+(4473764477/10000000000 : ℝ)*X 1 1+(1055840709/2500000000 : ℝ)*X 1 2+(4346812737/10000000000 : ℝ)*X 2 0+(4473764477/10000000000 : ℝ)*X 2 1+(1055840709/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (175885248614405779893194709/16568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204726239/10000000000000 : ℝ)*(base19) + (1911755339/100000000000000 : ℝ)*(base23) + (37339/48828125000 : ℝ)*(lower2) + (132580693/50000000000000 : ℝ)*(upper3) + (171187543/100000000000000 : ℝ)*(upper5) + (603942351286247/10000000000000 : ℝ)*(major0) + (603942351286247/10000000000000 : ℝ)*(major1) + (603942351286247/10000000000000 : ℝ)*(major2) + (4052700435899577/50000000000000 : ℝ)*(sp0) + (2026363903348513/25000000000000 : ℝ)*(sp1) + (8105455748901103/100000000000000 : ℝ)*(sp2) + (124167468287217/3125000000000 : ℝ)*(sp3) + (7098607161/12500000000000 : ℝ)*(sp4) + (15013014091/50000000000000 : ℝ)*(sp7) + (1986694505609563/50000000000000 : ℝ)*(f.failure) + (4052728830328221/50000000000000 : ℝ)*(f.sum) + (4161546951563/1325500000000000000000000000 : ℝ)*base65 + (329208658955974199/33137500000000000000000000000000 : ℝ)*base68 + (871674998329724199/33137500000000000000000000000000 : ℝ)*base70 + (176257724822999199/33137500000000000000000000000000 : ℝ)*base72 + (1168091166489/662750000000000000000000000 : ℝ)*base74 + (642823823536824199/33137500000000000000000000000000 : ℝ)*base76 + (566652479886224199/33137500000000000000000000000000 : ℝ)*base78 + (171695937540061699/33137500000000000000000000000000 : ℝ)*base80 + (6391956485803/2651000000000000000000000000 : ℝ)*base82 + (2227837/312500000000000000000 : ℝ)*base89 + (2227837/312500000000000000000 : ℝ)*base91 + (2227837/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294680718814834167815657253/82843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127179831/25000000000000 : ℝ)*(base19) + (588534621/50000000000000 : ℝ)*(base23) + (85708601/100000000000000 : ℝ)*(upper3) + (23433933/25000000000000 : ℝ)*(lower4) + (3035065081367647/50000000000000 : ℝ)*(major0) + (3035065081367647/50000000000000 : ℝ)*(major1) + (3035065081367647/50000000000000 : ℝ)*(major2) + (17651059977/100000000000000 : ℝ)*(sp1) + (46783342369/100000000000000 : ℝ)*(sp2) + (191722693/10000000000000 : ℝ)*(sp3) + (1018333628113723/12500000000000 : ℝ)*(sp4) + (4073325432565241/50000000000000 : ℝ)*(sp5) + (8146621064498171/100000000000000 : ℝ)*(sp6) + (1996794632382491/50000000000000 : ℝ)*(sp7) + (499198897748989/12500000000000 : ℝ)*(f.failure) + (1018333628113723/12500000000000 : ℝ)*(f.sum) + (13654878104481/3313750000000000000000000000 : ℝ)*base65 + (2314033180336482999/165687500000000000000000000000000 : ℝ)*base68 + (1178801484675232999/165687500000000000000000000000000 : ℝ)*base70 + (228915827729045499/165687500000000000000000000000000 : ℝ)*base72 + (9525791077921/13255000000000000000000000000 : ℝ)*base74 + (1749355502577517001/165687500000000000000000000000000 : ℝ)*base75 + (1203924618830170499/165687500000000000000000000000000 : ℝ)*base78 + (2641937523610829501/165687500000000000000000000000000 : ℝ)*base79 + (13157378719911/13255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (484289/78125000000000000000 : ℝ)*base90 + (484289/78125000000000000000 : ℝ)*base92 + (484289/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1270_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1270_s7_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1053342291/5000000000 : ℝ)*x 0 + (5390644869/10000000000 : ℝ)*x 1 + (5267599561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053342291/5000000000 : ℝ)^529 ≤ (12814189234623/100000000000000 : ℝ)^401 := by
    have hnat : (1053342291 : ℕ)^529*100000000000000^401 ≤ 12814189234623^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053342291 5000000000 12814189234623 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390644869/10000000000 : ℝ)^529 ≤ (44256789392691/100000000000000 : ℝ)^401 := by
    have hnat : (5390644869 : ℕ)^529*100000000000000^401 ≤ 44256789392691^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390644869 10000000000 44256789392691 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267599561/10000000000 : ℝ)^529 ≤ (1341531917493/3125000000000 : ℝ)^401 := by
    have hnat : (5267599561 : ℕ)^529*3125000000000^401 ≤ 1341531917493^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267599561 10000000000 1341531917493 3125000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1053342291/5000000000 : ℝ), (5390644869/10000000000 : ℝ), (5267599561/10000000000 : ℝ)] ![(12814189234623/100000000000000 : ℝ), (44256789392691/100000000000000 : ℝ), (1341531917493/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1053342291/5000000000 : ℝ)|^529 ≤ (12814189234623/100000000000000 : ℝ)^401
        have hw : |(-1053342291/5000000000 : ℝ)|=(1053342291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390644869/10000000000 : ℝ)|^529 ≤ (44256789392691/100000000000000 : ℝ)^401
        have hw : |(5390644869/10000000000 : ℝ)|=(5390644869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267599561/10000000000 : ℝ)|^529 ≤ (1341531917493/3125000000000 : ℝ)^401
        have hw : |(5267599561/10000000000 : ℝ)|=(5267599561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344146761/10000000000 : ℝ)*x 0 + (-2169064717/10000000000 : ℝ)*x 1 + (329224993/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344146761/10000000000 : ℝ)^529 ≤ (43753883996567/100000000000000 : ℝ)^401 := by
    have hnat : (5344146761 : ℕ)^529*100000000000000^401 ≤ 43753883996567^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344146761 10000000000 43753883996567 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169064717/10000000000 : ℝ)^529 ≤ (13317091109901/100000000000000 : ℝ)^401 := by
    have hnat : (2169064717 : ℕ)^529*100000000000000^401 ≤ 13317091109901^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169064717 10000000000 13317091109901 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329224993/625000000 : ℝ)^529 ≤ (21464512437679/50000000000000 : ℝ)^401 := by
    have hnat : (329224993 : ℕ)^529*50000000000000^401 ≤ 21464512437679^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329224993 625000000 21464512437679 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344146761/10000000000 : ℝ), (-2169064717/10000000000 : ℝ), (329224993/625000000 : ℝ)] ![(43753883996567/100000000000000 : ℝ), (13317091109901/100000000000000 : ℝ), (21464512437679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344146761/10000000000 : ℝ)|^529 ≤ (43753883996567/100000000000000 : ℝ)^401
        have hw : |(5344146761/10000000000 : ℝ)|=(5344146761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2169064717/10000000000 : ℝ)|^529 ≤ (13317091109901/100000000000000 : ℝ)^401
        have hw : |(-2169064717/10000000000 : ℝ)|=(2169064717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329224993/625000000 : ℝ)|^529 ≤ (21464512437679/50000000000000 : ℝ)^401
        have hw : |(329224993/625000000 : ℝ)|=(329224993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5344146901/10000000000 : ℝ)*x 0 + (329224987/625000000 : ℝ)*x 1 + (-1084532329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344146901/10000000000 : ℝ)^529 ≤ (2734617844291/6250000000000 : ℝ)^401 := by
    have hnat : (5344146901 : ℕ)^529*6250000000000^401 ≤ 2734617844291^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344146901 10000000000 2734617844291 6250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329224987/625000000 : ℝ)^529 ≤ (42929023843261/100000000000000 : ℝ)^401 := by
    have hnat : (329224987 : ℕ)^529*100000000000000^401 ≤ 42929023843261^401*625000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329224987 625000000 42929023843261 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084532329/5000000000 : ℝ)^529 ≤ (6658545316021/50000000000000 : ℝ)^401 := by
    have hnat : (1084532329 : ℕ)^529*50000000000000^401 ≤ 6658545316021^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084532329 5000000000 6658545316021 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344146901/10000000000 : ℝ), (329224987/625000000 : ℝ), (-1084532329/5000000000 : ℝ)] ![(2734617844291/6250000000000 : ℝ), (42929023843261/100000000000000 : ℝ), (6658545316021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344146901/10000000000 : ℝ)|^529 ≤ (2734617844291/6250000000000 : ℝ)^401
        have hw : |(5344146901/10000000000 : ℝ)|=(5344146901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329224987/625000000 : ℝ)|^529 ≤ (42929023843261/100000000000000 : ℝ)^401
        have hw : |(329224987/625000000 : ℝ)|=(329224987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1084532329/5000000000 : ℝ)|^529 ≤ (6658545316021/50000000000000 : ℝ)^401
        have hw : |(-1084532329/5000000000 : ℝ)|=(1084532329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346811947/10000000000 : ℝ)*x 0 + (1055764857/2500000000 : ℝ)*x 1 + (894812627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346811947/10000000000 : ℝ)^529 ≤ (33317642673493/100000000000000 : ℝ)^401 := by
    have hnat : (4346811947 : ℕ)^529*100000000000000^401 ≤ 33317642673493^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346811947 10000000000 33317642673493 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055764857/2500000000 : ℝ)^529 ≤ (16036022259807/50000000000000 : ℝ)^401 := by
    have hnat : (1055764857 : ℕ)^529*50000000000000^401 ≤ 16036022259807^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055764857 2500000000 16036022259807 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894812627/2000000000 : ℝ)^529 ≤ (34610312801779/100000000000000 : ℝ)^401 := by
    have hnat : (894812627 : ℕ)^529*100000000000000^401 ≤ 34610312801779^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894812627 2000000000 34610312801779 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346811947/10000000000 : ℝ), (1055764857/2500000000 : ℝ), (894812627/2000000000 : ℝ)] ![(33317642673493/100000000000000 : ℝ), (16036022259807/50000000000000 : ℝ), (34610312801779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346811947/10000000000 : ℝ)|^529 ≤ (33317642673493/100000000000000 : ℝ)^401
        have hw : |(4346811947/10000000000 : ℝ)|=(4346811947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055764857/2500000000 : ℝ)|^529 ≤ (16036022259807/50000000000000 : ℝ)^401
        have hw : |(1055764857/2500000000 : ℝ)|=(1055764857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(894812627/2000000000 : ℝ)|^529 ≤ (34610312801779/100000000000000 : ℝ)^401
        have hw : |(894812627/2000000000 : ℝ)|=(894812627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106689491/10000000000 : ℝ)*x 0 + (5267910749/10000000000 : ℝ)*x 1 + (1347583081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106689491/10000000000 : ℝ)^529 ≤ (6407114312771/50000000000000 : ℝ)^401 := by
    have hnat : (2106689491 : ℕ)^529*50000000000000^401 ≤ 6407114312771^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106689491 10000000000 6407114312771 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267910749/10000000000 : ℝ)^529 ≤ (42932366978691/100000000000000 : ℝ)^401 := by
    have hnat : (5267910749 : ℕ)^529*100000000000000^401 ≤ 42932366978691^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267910749 10000000000 42932366978691 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347583081/2500000000 : ℝ)^529 ≤ (44253404389993/100000000000000 : ℝ)^401 := by
    have hnat : (1347583081 : ℕ)^529*100000000000000^401 ≤ 44253404389993^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347583081 2500000000 44253404389993 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106689491/10000000000 : ℝ), (5267910749/10000000000 : ℝ), (1347583081/2500000000 : ℝ)] ![(6407114312771/50000000000000 : ℝ), (42932366978691/100000000000000 : ℝ), (44253404389993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106689491/10000000000 : ℝ)|^529 ≤ (6407114312771/50000000000000 : ℝ)^401
        have hw : |(-2106689491/10000000000 : ℝ)|=(2106689491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267910749/10000000000 : ℝ)|^529 ≤ (42932366978691/100000000000000 : ℝ)^401
        have hw : |(5267910749/10000000000 : ℝ)|=(5267910749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347583081/2500000000 : ℝ)|^529 ≤ (44253404389993/100000000000000 : ℝ)^401
        have hw : |(1347583081/2500000000 : ℝ)|=(1347583081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_5 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (664086271/1250000000 : ℝ)*x 0 + (-2046332207/10000000000 : ℝ)*x 1 + (5390332891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664086271/1250000000 : ℝ)^529 ≤ (21707226114611/50000000000000 : ℝ)^401 := by
    have hnat : (664086271 : ℕ)^529*50000000000000^401 ≤ 21707226114611^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664086271 1250000000 21707226114611 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2046332207/10000000000 : ℝ)^529 ≤ (12332137228127/100000000000000 : ℝ)^401 := by
    have hnat : (2046332207 : ℕ)^529*100000000000000^401 ≤ 12332137228127^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046332207 10000000000 12332137228127 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390332891/10000000000 : ℝ)^529 ≤ (44253410530801/100000000000000 : ℝ)^401 := by
    have hnat : (5390332891 : ℕ)^529*100000000000000^401 ≤ 44253410530801^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390332891 10000000000 44253410530801 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664086271/1250000000 : ℝ), (-2046332207/10000000000 : ℝ), (5390332891/10000000000 : ℝ)] ![(21707226114611/50000000000000 : ℝ), (12332137228127/100000000000000 : ℝ), (44253410530801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664086271/1250000000 : ℝ)|^529 ≤ (21707226114611/50000000000000 : ℝ)^401
        have hw : |(664086271/1250000000 : ℝ)|=(664086271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2046332207/10000000000 : ℝ)|^529 ≤ (12332137228127/100000000000000 : ℝ)^401
        have hw : |(-2046332207/10000000000 : ℝ)|=(2046332207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390332891/10000000000 : ℝ)|^529 ≤ (44253410530801/100000000000000 : ℝ)^401
        have hw : |(5390332891/10000000000 : ℝ)|=(5390332891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_6 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656344543/5000000000 : ℝ)*x 0 + (1078066841/2000000000 : ℝ)*x 1 + (-511582971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656344543/5000000000 : ℝ)^529 ≤ (4341444056493/10000000000000 : ℝ)^401 := by
    have hnat : (2656344543 : ℕ)^529*10000000000000^401 ≤ 4341444056493^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656344543 5000000000 4341444056493 10000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078066841/2000000000 : ℝ)^529 ≤ (1106335619047/2500000000000 : ℝ)^401 := by
    have hnat : (1078066841 : ℕ)^529*2500000000000^401 ≤ 1106335619047^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078066841 2000000000 1106335619047 2500000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511582971/2500000000 : ℝ)^529 ≤ (154151683253/1250000000000 : ℝ)^401 := by
    have hnat : (511582971 : ℕ)^529*1250000000000^401 ≤ 154151683253^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511582971 2500000000 154151683253 1250000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656344543/5000000000 : ℝ), (1078066841/2000000000 : ℝ), (-511582971/2500000000 : ℝ)] ![(4341444056493/10000000000000 : ℝ), (1106335619047/2500000000000 : ℝ), (154151683253/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656344543/5000000000 : ℝ)|^529 ≤ (4341444056493/10000000000000 : ℝ)^401
        have hw : |(2656344543/5000000000 : ℝ)|=(2656344543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078066841/2000000000 : ℝ)|^529 ≤ (1106335619047/2500000000000 : ℝ)^401
        have hw : |(1078066841/2000000000 : ℝ)|=(1078066841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511582971/2500000000 : ℝ)|^529 ≤ (154151683253/1250000000000 : ℝ)^401
        have hw : |(-511582971/2500000000 : ℝ)|=(511582971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s7_7 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346822291/10000000000 : ℝ)*x 0 + (894685847/2000000000 : ℝ)*x 1 + (4223694649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346822291/10000000000 : ℝ)^529 ≤ (16658873633339/50000000000000 : ℝ)^401 := by
    have hnat : (4346822291 : ℕ)^529*50000000000000^401 ≤ 16658873633339^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346822291 10000000000 16658873633339 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (894685847/2000000000 : ℝ)^529 ≤ (34603843973147/100000000000000 : ℝ)^401 := by
    have hnat : (894685847 : ℕ)^529*100000000000000^401 ≤ 34603843973147^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894685847 2000000000 34603843973147 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223694649/10000000000 : ℝ)^529 ≤ (32078408751941/100000000000000 : ℝ)^401 := by
    have hnat : (4223694649 : ℕ)^529*100000000000000^401 ≤ 32078408751941^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223694649 10000000000 32078408751941 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346822291/10000000000 : ℝ), (894685847/2000000000 : ℝ), (4223694649/10000000000 : ℝ)] ![(16658873633339/50000000000000 : ℝ), (34603843973147/100000000000000 : ℝ), (32078408751941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346822291/10000000000 : ℝ)|^529 ≤ (16658873633339/50000000000000 : ℝ)^401
        have hw : |(4346822291/10000000000 : ℝ)|=(4346822291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(894685847/2000000000 : ℝ)|^529 ≤ (34603843973147/100000000000000 : ℝ)^401
        have hw : |(894685847/2000000000 : ℝ)|=(894685847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223694649/10000000000 : ℝ)|^529 ≤ (32078408751941/100000000000000 : ℝ)^401
        have hw : |(4223694649/10000000000 : ℝ)|=(4223694649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11513/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11509/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11509/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11509/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11509/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (527184805140111/4000000000000000000 : ℝ) := by
    have hpowers : (11509/100000 : ℝ)^8463 ≤ (527184805140111/4000000000000000000 : ℝ)^2048 := by
      have hnat : (11509 : ℕ)^8463*4000000000000000000^2048 ≤ 527184805140111^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11509 100000 527184805140111 4000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11509/100000 : ℝ)) (X := (527184805140111/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14123/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (15352976662818243/50000000000000000000 : ℝ) := by
    have hpowers : (14123/100000 : ℝ)^8463 ≤ (15352976662818243/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14123 : ℕ)^8463*50000000000000000000^2048 ≤ 15352976662818243^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14123 100000 15352976662818243 50000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14123/100000 : ℝ)) (X := (15352976662818243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000527184805140111/2000000000000000000 : ℝ) ≤ (10000637815571127/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (2000527184805140111/2000000000000000000 : ℝ)^2048 ≤ (10000637815571127/10000000000000000 : ℝ)^8463 := by
      have hnat : (2000527184805140111 : ℕ)^2048*10000000000000000^8463 ≤ 10000637815571127^8463*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000527184805140111 2000000000000000000 10000637815571127 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000637815571127/10000000000000000 : ℝ)) (X := (2000527184805140111/2000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043885573454139261/100000000000000000000 : ℝ) ≤ (500053091521417/500000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (100043885573454139261/100000000000000000000 : ℝ)^2048 ≤ (500053091521417/500000000000000 : ℝ)^8463 := by
      have hnat : (100043885573454139261 : ℕ)^2048*500000000000000^8463 ≤ 500053091521417^8463*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043885573454139261 100000000000000000000 500053091521417 500000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500053091521417/500000000000000 : ℝ)) (X := (100043885573454139261/100000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015352976662818243/25000000000000000000 : ℝ) ≤ (10001485845285553/10000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (25015352976662818243/25000000000000000000 : ℝ)^2048 ≤ (10001485845285553/10000000000000000 : ℝ)^8463 := by
      have hnat : (25015352976662818243 : ℕ)^2048*10000000000000000^8463 ≤ 10001485845285553^8463*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015352976662818243 25000000000000000000 10001485845285553 10000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001485845285553/10000000000000000 : ℝ)) (X := (25015352976662818243/25000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(527184805140111/4000000000000000000 : ℝ) ≤ ((3266488409489949643/3267500000000000000 : ℝ)+2*(424014857213/261400000000000 : ℝ)*(11509/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (3266488409489949643/3267500000000000000 : ℝ)+2*(424014857213/261400000000000 : ℝ)*(11509/100000 : ℝ)=(10000637815571127/10000000000000000 : ℝ) by norm_num, show 1+2*(527184805140111/4000000000000000000 : ℝ)=(2000527184805140111/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15352976662818243/50000000000000000000 : ℝ)+(527184805140111/4000000000000000000 : ℝ) ≤ ((3266488409489949643/3267500000000000000 : ℝ)+(424014857213/261400000000000 : ℝ)*((14123/100000 : ℝ)+(11509/100000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (3266488409489949643/3267500000000000000 : ℝ)+(424014857213/261400000000000 : ℝ)*((14123/100000 : ℝ)+(11509/100000 : ℝ))=(500053091521417/500000000000000 : ℝ) by norm_num, show 1+(15352976662818243/50000000000000000000 : ℝ)+(527184805140111/4000000000000000000 : ℝ)=(100043885573454139261/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15352976662818243/50000000000000000000 : ℝ) ≤ ((3266488409489949643/3267500000000000000 : ℝ)+2*(424014857213/261400000000000 : ℝ)*(14123/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (3266488409489949643/3267500000000000000 : ℝ)+2*(424014857213/261400000000000 : ℝ)*(14123/100000 : ℝ)=(10001485845285553/10000000000000000 : ℝ) by norm_num, show 1+2*(15352976662818243/50000000000000000000 : ℝ)=(25015352976662818243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3266488409489949643/3267500000000000000 : ℝ)*(X 1 0+X 2 0)+(424014857213/261400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (3266488409489949643/3267500000000000000 : ℝ)) (alpha := (424014857213/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3266488409489949643/3267500000000000000 : ℝ)*(X 0 1+X 2 1)+(424014857213/261400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (3266488409489949643/3267500000000000000 : ℝ)) (alpha := (424014857213/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3266488409489949643/3267500000000000000 : ℝ)*(X 0 2+X 1 2)+(424014857213/261400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11509/100000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (3266488409489949643/3267500000000000000 : ℝ)) (alpha := (424014857213/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1053342291/5000000000 : ℝ)*X 0 0+(5390644869/10000000000 : ℝ)*X 0 1+(5267599561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344146761/10000000000 : ℝ)*X 1 0+(-2169064717/10000000000 : ℝ)*X 1 1+(329224993/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344146901/10000000000 : ℝ)*X 2 0+(329224987/625000000 : ℝ)*X 2 1+(-1084532329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346811947/10000000000 : ℝ)*X 0 0+(1055764857/2500000000 : ℝ)*X 0 1+(894812627/2000000000 : ℝ)*X 0 2+(4346811947/10000000000 : ℝ)*X 1 0+(1055764857/2500000000 : ℝ)*X 1 1+(894812627/2000000000 : ℝ)*X 1 2+(4346811947/10000000000 : ℝ)*X 2 0+(1055764857/2500000000 : ℝ)*X 2 1+(894812627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2106689491/10000000000 : ℝ)*X 0 0+(5267910749/10000000000 : ℝ)*X 0 1+(1347583081/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664086271/1250000000 : ℝ)*X 1 0+(-2046332207/10000000000 : ℝ)*X 1 1+(5390332891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656344543/5000000000 : ℝ)*X 2 0+(1078066841/2000000000 : ℝ)*X 2 1+(-511582971/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4346822291/10000000000 : ℝ)*X 0 0+(894685847/2000000000 : ℝ)*X 0 1+(4223694649/10000000000 : ℝ)*X 0 2+(4346822291/10000000000 : ℝ)*X 1 0+(894685847/2000000000 : ℝ)*X 1 1+(4223694649/10000000000 : ℝ)*X 1 2+(4346822291/10000000000 : ℝ)*X 2 0+(894685847/2000000000 : ℝ)*X 2 1+(4223694649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83338457843253394685585301/20421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309381701/25000000000000 : ℝ)*(base19) + (2275929/200000000000 : ℝ)*(base23) + (33397647/20000000000000 : ℝ)*(lower2) + (190859941/100000000000000 : ℝ)*(upper3) + (98210563/100000000000000 : ℝ)*(upper5) + (1513904498592369/25000000000000 : ℝ)*(major0) + (1513904498592369/25000000000000 : ℝ)*(major1) + (1513904498592369/25000000000000 : ℝ)*(major2) + (1015892316502551/12500000000000 : ℝ)*(sp0) + (507949444649313/6250000000000 : ℝ)*(sp1) + (507949450871957/6250000000000 : ℝ)*(sp2) + (796804355538297/20000000000000 : ℝ)*(sp3) + (10763979081/20000000000000 : ℝ)*(sp4) + (5430775889/25000000000000 : ℝ)*(sp7) + (24900271879969/625000000000 : ℝ)*(f.failure) + (2031798087978953/25000000000000 : ℝ)*(f.sum) + (14218069876447/3267500000000000000000000000 : ℝ)*base65 + (498531758339650733/81687500000000000000000000000000 : ℝ)*base68 + (431806491279025733/81687500000000000000000000000000 : ℝ)*base70 + (1137263968770525733/81687500000000000000000000000000 : ℝ)*base72 + (22238406971723/3267500000000000000000000000 : ℝ)*base74 + (614363268014775733/81687500000000000000000000000000 : ℝ)*base76 + (137675237581474267/81687500000000000000000000000000 : ℝ)*base77 + (1310965589248963233/81687500000000000000000000000000 : ℝ)*base80 + (46555247945111/6535000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (30019/3906250000000000000 : ℝ)*base90 + (30019/3906250000000000000 : ℝ)*base92 + (30019/3906250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2075236705083984922161201219/163375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20574537/1562500000000 : ℝ)*(base19) + (327439443/100000000000000 : ℝ)*(base23) + (44858149/50000000000000 : ℝ)*(lower2) + (1070137393/100000000000000 : ℝ)*(upper3) + (13532157/5000000000000 : ℝ)*(lower4) + (225202297/100000000000000 : ℝ)*(upper5) + (6086346013302989/100000000000000 : ℝ)*(major0) + (6086346013302989/100000000000000 : ℝ)*(major1) + (6086346013302989/100000000000000 : ℝ)*(major2) + (56360106869/100000000000000 : ℝ)*(sp2) + (4084215936369219/50000000000000 : ℝ)*(sp4) + (8168430555968069/100000000000000 : ℝ)*(sp5) + (4084187592596063/50000000000000 : ℝ)*(sp6) + (2002129865228921/50000000000000 : ℝ)*(sp7) + (2002129865228921/50000000000000 : ℝ)*(f.failure) + (4084215936369219/50000000000000 : ℝ)*(f.sum) + (232808278510177/13070000000000000000000000000 : ℝ)*base65 + (5358401381948904573/326750000000000000000000000000000 : ℝ)*base68 + (2183225041934595427/326750000000000000000000000000000 : ℝ)*base69 + (5110073710207595427/326750000000000000000000000000000 : ℝ)*base71 + (56881888402433/13070000000000000000000000000 : ℝ)*base74 + (4820820454417345427/326750000000000000000000000000000 : ℝ)*base75 + (9452498146109845427/326750000000000000000000000000000 : ℝ)*base77 + (1735061161426904573/326750000000000000000000000000000 : ℝ)*base80 + (45776509134617/13070000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2138121/312500000000000000000 : ℝ)*base90 + (2138121/312500000000000000000 : ℝ)*base92 + (2138121/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1270_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11509/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1270_s8_0 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2672070041/5000000000 : ℝ)*x 0 + (5267630817/10000000000 : ℝ)*x 1 + (-271129071/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672070041/5000000000 : ℝ)^529 ≤ (43753811859099/100000000000000 : ℝ)^401 := by
    have hnat : (2672070041 : ℕ)^529*100000000000000^401 ≤ 43753811859099^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672070041 5000000000 43753811859099 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267630817/10000000000 : ℝ)^529 ≤ (42929357393871/100000000000000 : ℝ)^401 := by
    have hnat : (5267630817 : ℕ)^529*100000000000000^401 ≤ 42929357393871^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267630817 10000000000 42929357393871 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271129071/1250000000 : ℝ)^529 ≤ (13316830725717/100000000000000 : ℝ)^401 := by
    have hnat : (271129071 : ℕ)^529*100000000000000^401 ≤ 13316830725717^401*1250000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271129071 1250000000 13316830725717 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672070041/5000000000 : ℝ), (5267630817/10000000000 : ℝ), (-271129071/1250000000 : ℝ)] ![(43753811859099/100000000000000 : ℝ), (42929357393871/100000000000000 : ℝ), (13316830725717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672070041/5000000000 : ℝ)|^529 ≤ (43753811859099/100000000000000 : ℝ)^401
        have hw : |(2672070041/5000000000 : ℝ)|=(2672070041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267630817/10000000000 : ℝ)|^529 ≤ (42929357393871/100000000000000 : ℝ)^401
        have hw : |(5267630817/10000000000 : ℝ)|=(5267630817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271129071/1250000000 : ℝ)|^529 ≤ (13316830725717/100000000000000 : ℝ)^401
        have hw : |(-271129071/1250000000 : ℝ)|=(271129071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s8_1 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2106688489/10000000000 : ℝ)*x 0 + (5267941123/10000000000 : ℝ)*x 1 + (2695151457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2106688489/10000000000 : ℝ)^529 ≤ (6407110292633/50000000000000 : ℝ)^401 := by
    have hnat : (2106688489 : ℕ)^529*50000000000000^401 ≤ 6407110292633^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106688489 10000000000 6407110292633 50000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267941123/10000000000 : ℝ)^529 ≤ (42932693536529/100000000000000 : ℝ)^401 := by
    have hnat : (5267941123 : ℕ)^529*100000000000000^401 ≤ 42932693536529^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267941123 10000000000 42932693536529 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695151457/5000000000 : ℝ)^529 ≤ (44253085869711/100000000000000 : ℝ)^401 := by
    have hnat : (2695151457 : ℕ)^529*100000000000000^401 ≤ 44253085869711^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695151457 5000000000 44253085869711 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2106688489/10000000000 : ℝ), (5267941123/10000000000 : ℝ), (2695151457/5000000000 : ℝ)] ![(6407110292633/50000000000000 : ℝ), (42932693536529/100000000000000 : ℝ), (44253085869711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2106688489/10000000000 : ℝ)|^529 ≤ (6407110292633/50000000000000 : ℝ)^401
        have hw : |(-2106688489/10000000000 : ℝ)|=(2106688489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267941123/10000000000 : ℝ)|^529 ≤ (42932693536529/100000000000000 : ℝ)^401
        have hw : |(5267941123/10000000000 : ℝ)|=(5267941123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695151457/5000000000 : ℝ)|^529 ≤ (44253085869711/100000000000000 : ℝ)^401
        have hw : |(2695151457/5000000000 : ℝ)|=(2695151457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s8_2 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5312699421/10000000000 : ℝ)*x 0 + (-1023180247/5000000000 : ℝ)*x 1 + (1347575729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312699421/10000000000 : ℝ)^529 ≤ (43414551979433/100000000000000 : ℝ)^401 := by
    have hnat : (5312699421 : ℕ)^529*100000000000000^401 ≤ 43414551979433^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312699421 10000000000 43414551979433 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023180247/5000000000 : ℝ)^529 ≤ (12332362113577/100000000000000 : ℝ)^401 := by
    have hnat : (1023180247 : ℕ)^529*100000000000000^401 ≤ 12332362113577^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023180247 5000000000 12332362113577 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347575729/2500000000 : ℝ)^529 ≤ (11063271472843/25000000000000 : ℝ)^401 := by
    have hnat : (1347575729 : ℕ)^529*25000000000000^401 ≤ 11063271472843^401*2500000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347575729 2500000000 11063271472843 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312699421/10000000000 : ℝ), (-1023180247/5000000000 : ℝ), (1347575729/2500000000 : ℝ)] ![(43414551979433/100000000000000 : ℝ), (12332362113577/100000000000000 : ℝ), (11063271472843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312699421/10000000000 : ℝ)|^529 ≤ (43414551979433/100000000000000 : ℝ)^401
        have hw : |(5312699421/10000000000 : ℝ)|=(5312699421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023180247/5000000000 : ℝ)|^529 ≤ (12332362113577/100000000000000 : ℝ)^401
        have hw : |(-1023180247/5000000000 : ℝ)|=(1023180247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347575729/2500000000 : ℝ)|^529 ≤ (11063271472843/25000000000000 : ℝ)^401
        have hw : |(1347575729/2500000000 : ℝ)|=(1347575729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s8_3 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2656349711/5000000000 : ℝ)*x 0 + (2695151457/5000000000 : ℝ)*x 1 + (-409272099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656349711/5000000000 : ℝ)^529 ≤ (43414551990213/100000000000000 : ℝ)^401 := by
    have hnat : (2656349711 : ℕ)^529*100000000000000^401 ≤ 43414551990213^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656349711 5000000000 43414551990213 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695151457/5000000000 : ℝ)^529 ≤ (44253085869711/100000000000000 : ℝ)^401 := by
    have hnat : (2695151457 : ℕ)^529*100000000000000^401 ≤ 44253085869711^401*5000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695151457 5000000000 44253085869711 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409272099/2000000000 : ℝ)^529 ≤ (12332362121527/100000000000000 : ℝ)^401 := by
    have hnat : (409272099 : ℕ)^529*100000000000000^401 ≤ 12332362121527^401*2000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409272099 2000000000 12332362121527 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656349711/5000000000 : ℝ), (2695151457/5000000000 : ℝ), (-409272099/2000000000 : ℝ)] ![(43414551990213/100000000000000 : ℝ), (44253085869711/100000000000000 : ℝ), (12332362121527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656349711/5000000000 : ℝ)|^529 ≤ (43414551990213/100000000000000 : ℝ)^401
        have hw : |(2656349711/5000000000 : ℝ)|=(2656349711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695151457/5000000000 : ℝ)|^529 ≤ (44253085869711/100000000000000 : ℝ)^401
        have hw : |(2695151457/5000000000 : ℝ)|=(2695151457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409272099/2000000000 : ℝ)|^529 ≤ (12332362121527/100000000000000 : ℝ)^401
        have hw : |(-409272099/2000000000 : ℝ)|=(409272099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1270_s8_4 (p : ℝ) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4346822527/10000000000 : ℝ)*x 0 + (4473367489/10000000000 : ℝ)*x 1 + (4223757299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346822527/10000000000 : ℝ)^529 ≤ (33317749652989/100000000000000 : ℝ)^401 := by
    have hnat : (4346822527 : ℕ)^529*100000000000000^401 ≤ 33317749652989^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346822527 10000000000 33317749652989 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473367489/10000000000 : ℝ)^529 ≤ (8650803470657/25000000000000 : ℝ)^401 := by
    have hnat : (4473367489 : ℕ)^529*25000000000000^401 ≤ 8650803470657^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473367489 10000000000 8650803470657 25000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223757299/10000000000 : ℝ)^529 ≤ (32079036454221/100000000000000 : ℝ)^401 := by
    have hnat : (4223757299 : ℕ)^529*100000000000000^401 ≤ 32079036454221^401*10000000000^529 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223757299 10000000000 32079036454221 100000000000000 529 401 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (529/128 : ℝ)) 529 401 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346822527/10000000000 : ℝ), (4473367489/10000000000 : ℝ), (4223757299/10000000000 : ℝ)] ![(33317749652989/100000000000000 : ℝ), (8650803470657/25000000000000 : ℝ), (32079036454221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346822527/10000000000 : ℝ)|^529 ≤ (33317749652989/100000000000000 : ℝ)^401
        have hw : |(4346822527/10000000000 : ℝ)|=(4346822527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473367489/10000000000 : ℝ)|^529 ≤ (8650803470657/25000000000000 : ℝ)^401
        have hw : |(4473367489/10000000000 : ℝ)|=(4473367489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223757299/10000000000 : ℝ)|^529 ≤ (32079036454221/100000000000000 : ℝ)^401
        have hw : |(4223757299/10000000000 : ℝ)|=(4223757299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1270_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11513/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11513/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11513/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11513/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11513/100000 : ℝ) ^ (8463/2048 : ℝ) ≤ (1319855908622709/10000000000000000000 : ℝ) := by
    have hpowers : (11513/100000 : ℝ)^8463 ≤ (1319855908622709/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11513 : ℕ)^8463*10000000000000000000^2048 ≤ 1319855908622709^2048*100000^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11513 100000 1319855908622709 10000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11513/100000 : ℝ)) (X := (1319855908622709/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (8463/2048 : ℝ) ≤ (7669752258277233/25000000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^8463 ≤ (7669752258277233/25000000000000000000 : ℝ)^2048 := by
      have hnat : (353 : ℕ)^8463*25000000000000000000^2048 ≤ 7669752258277233^2048*2500^8463 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 7669752258277233 25000000000000000000 8463 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (7669752258277233/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001319855908622709/5000000000000000000 : ℝ) ≤ (5000319366006429/5000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (5001319855908622709/5000000000000000000 : ℝ)^2048 ≤ (5000319366006429/5000000000000000 : ℝ)^8463 := by
      have hnat : (5001319855908622709 : ℕ)^2048*5000000000000000^8463 ≤ 5000319366006429^8463*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001319855908622709 5000000000000000000 5000319366006429 5000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000319366006429/5000000000000000 : ℝ)) (X := (5001319855908622709/5000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021938784059668011/50000000000000000000 : ℝ) ≤ (5000530818384001/5000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (50021938784059668011/50000000000000000000 : ℝ)^2048 ≤ (5000530818384001/5000000000000000 : ℝ)^8463 := by
      have hnat : (50021938784059668011 : ℕ)^2048*5000000000000000^8463 ≤ 5000530818384001^8463*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021938784059668011 50000000000000000000 5000530818384001 5000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000530818384001/5000000000000000 : ℝ)) (X := (50021938784059668011/50000000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507669752258277233/12500000000000000000 : ℝ) ≤ (5000742270761573/5000000000000000 : ℝ) ^ (8463/2048 : ℝ) := by
    have hpowers : (12507669752258277233/12500000000000000000 : ℝ)^2048 ≤ (5000742270761573/5000000000000000 : ℝ)^8463 := by
      have hnat : (12507669752258277233 : ℕ)^2048*5000000000000000^8463 ≤ 5000742270761573^8463*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507669752258277233 12500000000000000000 5000742270761573 5000000000000000 2048 8463 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000742270761573/5000000000000000 : ℝ)) (X := (12507669752258277233/12500000000000000000 : ℝ)) (by norm_num) 8463 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1319855908622709/10000000000000000000 : ℝ) ≤ ((13030963684732787531/13035000000000000000 : ℝ)+2*(52863094393/32587500000000 : ℝ)*(11513/100000 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (13030963684732787531/13035000000000000000 : ℝ)+2*(52863094393/32587500000000 : ℝ)*(11513/100000 : ℝ)=(5000319366006429/5000000000000000 : ℝ) by norm_num, show 1+2*(1319855908622709/10000000000000000000 : ℝ)=(5001319855908622709/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7669752258277233/25000000000000000000 : ℝ)+(1319855908622709/10000000000000000000 : ℝ) ≤ ((13030963684732787531/13035000000000000000 : ℝ)+(52863094393/32587500000000 : ℝ)*((353/2500 : ℝ)+(11513/100000 : ℝ)))^(8463/2048 : ℝ) := by
    rw [show (13030963684732787531/13035000000000000000 : ℝ)+(52863094393/32587500000000 : ℝ)*((353/2500 : ℝ)+(11513/100000 : ℝ))=(5000530818384001/5000000000000000 : ℝ) by norm_num, show 1+(7669752258277233/25000000000000000000 : ℝ)+(1319855908622709/10000000000000000000 : ℝ)=(50021938784059668011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7669752258277233/25000000000000000000 : ℝ) ≤ ((13030963684732787531/13035000000000000000 : ℝ)+2*(52863094393/32587500000000 : ℝ)*(353/2500 : ℝ))^(8463/2048 : ℝ) := by
    rw [show (13030963684732787531/13035000000000000000 : ℝ)+2*(52863094393/32587500000000 : ℝ)*(353/2500 : ℝ)=(5000742270761573/5000000000000000 : ℝ) by norm_num, show 1+2*(7669752258277233/25000000000000000000 : ℝ)=(12507669752258277233/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13030963684732787531/13035000000000000000 : ℝ)*(X 1 0+X 2 0)+(52863094393/32587500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11513/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (13030963684732787531/13035000000000000000 : ℝ)) (alpha := (52863094393/32587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13030963684732787531/13035000000000000000 : ℝ)*(X 0 1+X 2 1)+(52863094393/32587500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11513/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (13030963684732787531/13035000000000000000 : ℝ)) (alpha := (52863094393/32587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13030963684732787531/13035000000000000000 : ℝ)*(X 0 2+X 1 2)+(52863094393/32587500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8463/2048 : ℝ)) (lo := (11513/100000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (13030963684732787531/13035000000000000000 : ℝ)) (alpha := (52863094393/32587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672070041/5000000000 : ℝ)*X 2 0+(5267630817/10000000000 : ℝ)*X 2 1+(-271129071/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2106688489/10000000000 : ℝ)*X 0 0+(5267941123/10000000000 : ℝ)*X 0 1+(2695151457/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312699421/10000000000 : ℝ)*X 1 0+(-1023180247/5000000000 : ℝ)*X 1 1+(1347575729/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656349711/5000000000 : ℝ)*X 2 0+(2695151457/5000000000 : ℝ)*X 2 1+(-409272099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4346822527/10000000000 : ℝ)*X 0 0+(4473367489/10000000000 : ℝ)*X 0 1+(4223757299/10000000000 : ℝ)*X 0 2+(4346822527/10000000000 : ℝ)*X 1 0+(4473367489/10000000000 : ℝ)*X 1 1+(4223757299/10000000000 : ℝ)*X 1 2+(4346822527/10000000000 : ℝ)*X 2 0+(4473367489/10000000000 : ℝ)*X 2 1+(4223757299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1270_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (654283586983238888707635711/108625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1073278411/100000000000000 : ℝ)*(base19) + (1167709941/100000000000000 : ℝ)*(base23) + (74824723/20000000000000 : ℝ)*(lower1) + (30564927/25000000000000 : ℝ)*(upper3) + (4220759/10000000000000 : ℝ)*(lower4) + (30505843/25000000000000 : ℝ)*(upper5) + (3044671402779781/50000000000000 : ℝ)*(major0) + (3044671402779781/50000000000000 : ℝ)*(major1) + (3044671402779781/50000000000000 : ℝ)*(major2) + (2272156761/100000000000000 : ℝ)*(sp0) + (8172454064315541/100000000000000 : ℝ)*(sp1) + (817245299103713/10000000000000 : ℝ)*(sp2) + (204311265611221/2500000000000 : ℝ)*(sp3) + (2003115673013043/50000000000000 : ℝ)*(sp4) + (2003115673013043/50000000000000 : ℝ)*(f.failure) + (8172454064315541/100000000000000 : ℝ)*(f.sum) + (57320902774127/13035000000000000000000000000 : ℝ)*base66 + (2063615398944720237/217250000000000000000000000000000 : ℝ)*base67 + (1523937607700029763/217250000000000000000000000000000 : ℝ)*base70 + (28307365332595970237/217250000000000000000000000000000 : ℝ)*base71 + (8281819554631/6517500000000000000000000000 : ℝ)*base74 + (10134746638353529763/217250000000000000000000000000000 : ℝ)*base76 + (292177037176029763/217250000000000000000000000000000 : ℝ)*base78 + (7041881950811779763/217250000000000000000000000000000 : ℝ)*base80 + (10320218724691/6517500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1628357/312500000000000000000 : ℝ)*base89 + (1628357/312500000000000000000 : ℝ)*base91 + (1628357/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1270_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1270_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1270_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1270_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1270_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1270_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8463/2048 : ℝ) ≤ p) (hpb : p ≤ (529/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9499799/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7071/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11513/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1270_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
