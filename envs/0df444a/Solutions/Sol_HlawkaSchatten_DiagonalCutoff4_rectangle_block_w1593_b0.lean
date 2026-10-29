-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1593_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:38.747777+00:00
-- url     : https://prove2.me/submissions/6e7c2661-92f1-4966-8632-01bf97890ee9

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
theorem support_rectangle_w1593_s0_0 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199772151/1250000000 : ℝ)*x 0 + (5860577829/10000000000 : ℝ)*x 1 + (4880020459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199772151/1250000000 : ℝ)^4691 ≤ (4788608334257/50000000000000 : ℝ)^3667 := by
    have hnat : (199772151 : ℕ)^4691*50000000000000^3667 ≤ 4788608334257^3667*1250000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199772151 1250000000 4788608334257 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5860577829/10000000000 : ℝ)^4691 ≤ (12620554329143/25000000000000 : ℝ)^3667 := by
    have hnat : (5860577829 : ℕ)^4691*25000000000000^3667 ≤ 12620554329143^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5860577829 10000000000 12620554329143 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880020459/10000000000 : ℝ)^4691 ≤ (3994056599347/10000000000000 : ℝ)^3667 := by
    have hnat : (4880020459 : ℕ)^4691*10000000000000^3667 ≤ 3994056599347^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880020459 10000000000 3994056599347 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199772151/1250000000 : ℝ), (5860577829/10000000000 : ℝ), (4880020459/10000000000 : ℝ)] ![(4788608334257/50000000000000 : ℝ), (12620554329143/25000000000000 : ℝ), (3994056599347/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199772151/1250000000 : ℝ)|^4691 ≤ (4788608334257/50000000000000 : ℝ)^3667
        have hw : |(-199772151/1250000000 : ℝ)|=(199772151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5860577829/10000000000 : ℝ)|^4691 ≤ (12620554329143/25000000000000 : ℝ)^3667
        have hw : |(5860577829/10000000000 : ℝ)|=(5860577829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880020459/10000000000 : ℝ)|^4691 ≤ (3994056599347/10000000000000 : ℝ)^3667
        have hw : |(4880020459/10000000000 : ℝ)|=(4880020459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_1 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5460777209/10000000000 : ℝ)*x 0 + (-2143202881/10000000000 : ℝ)*x 1 + (4880020327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5460777209/10000000000 : ℝ)^4691 ≤ (4611938044573/10000000000000 : ℝ)^3667 := by
    have hnat : (5460777209 : ℕ)^4691*10000000000000^3667 ≤ 4611938044573^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460777209 10000000000 4611938044573 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143202881/10000000000 : ℝ)^4691 ≤ (3485013733249/25000000000000 : ℝ)^3667 := by
    have hnat : (2143202881 : ℕ)^4691*25000000000000^3667 ≤ 3485013733249^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143202881 10000000000 3485013733249 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880020327/10000000000 : ℝ)^4691 ≤ (39940564611429/100000000000000 : ℝ)^3667 := by
    have hnat : (4880020327 : ℕ)^4691*100000000000000^3667 ≤ 39940564611429^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880020327 10000000000 39940564611429 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5460777209/10000000000 : ℝ), (-2143202881/10000000000 : ℝ), (4880020327/10000000000 : ℝ)] ![(4611938044573/10000000000000 : ℝ), (3485013733249/25000000000000 : ℝ), (39940564611429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5460777209/10000000000 : ℝ)|^4691 ≤ (4611938044573/10000000000000 : ℝ)^3667
        have hw : |(5460777209/10000000000 : ℝ)|=(5460777209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2143202881/10000000000 : ℝ)|^4691 ≤ (3485013733249/25000000000000 : ℝ)^3667
        have hw : |(-2143202881/10000000000 : ℝ)|=(2143202881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880020327/10000000000 : ℝ)|^4691 ≤ (39940564611429/100000000000000 : ℝ)^3667
        have hw : |(4880020327/10000000000 : ℝ)|=(4880020327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_2 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5460777237/10000000000 : ℝ)*x 0 + (4880020247/10000000000 : ℝ)*x 1 + (-428640589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5460777237/10000000000 : ℝ)^4691 ≤ (46119380748241/100000000000000 : ℝ)^3667 := by
    have hnat : (5460777237 : ℕ)^4691*100000000000000^3667 ≤ 46119380748241^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460777237 10000000000 46119380748241 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4880020247/10000000000 : ℝ)^4691 ≤ (9985140943457/25000000000000 : ℝ)^3667 := by
    have hnat : (4880020247 : ℕ)^4691*25000000000000^3667 ≤ 9985140943457^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880020247 10000000000 9985140943457 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428640589/2000000000 : ℝ)^4691 ≤ (2788011093103/20000000000000 : ℝ)^3667 := by
    have hnat : (428640589 : ℕ)^4691*20000000000000^3667 ≤ 2788011093103^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428640589 2000000000 2788011093103 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5460777237/10000000000 : ℝ), (4880020247/10000000000 : ℝ), (-428640589/2000000000 : ℝ)] ![(46119380748241/100000000000000 : ℝ), (9985140943457/25000000000000 : ℝ), (2788011093103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5460777237/10000000000 : ℝ)|^4691 ≤ (46119380748241/100000000000000 : ℝ)^3667
        have hw : |(5460777237/10000000000 : ℝ)|=(5460777237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4880020247/10000000000 : ℝ)|^4691 ≤ (9985140943457/25000000000000 : ℝ)^3667
        have hw : |(4880020247/10000000000 : ℝ)|=(4880020247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428640589/2000000000 : ℝ)|^4691 ≤ (2788011093103/20000000000000 : ℝ)^3667
        have hw : |(-428640589/2000000000 : ℝ)|=(428640589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_3 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4118215503/10000000000 : ℝ)*x 0 + (3071882567/10000000000 : ℝ)*x 1 + (5427599379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4118215503/10000000000 : ℝ)^4691 ≤ (32145308729571/100000000000000 : ℝ)^3667 := by
    have hnat : (4118215503 : ℕ)^4691*100000000000000^3667 ≤ 32145308729571^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118215503 10000000000 32145308729571 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3071882567/10000000000 : ℝ)^4691 ≤ (5523364674931/25000000000000 : ℝ)^3667 := by
    have hnat : (3071882567 : ℕ)^4691*25000000000000^3667 ≤ 5523364674931^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071882567 10000000000 5523364674931 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427599379/10000000000 : ℝ)^4691 ≤ (45761232556471/100000000000000 : ℝ)^3667 := by
    have hnat : (5427599379 : ℕ)^4691*100000000000000^3667 ≤ 45761232556471^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427599379 10000000000 45761232556471 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4118215503/10000000000 : ℝ), (3071882567/10000000000 : ℝ), (5427599379/10000000000 : ℝ)] ![(32145308729571/100000000000000 : ℝ), (5523364674931/25000000000000 : ℝ), (45761232556471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4118215503/10000000000 : ℝ)|^4691 ≤ (32145308729571/100000000000000 : ℝ)^3667
        have hw : |(4118215503/10000000000 : ℝ)|=(4118215503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3071882567/10000000000 : ℝ)|^4691 ≤ (5523364674931/25000000000000 : ℝ)^3667
        have hw : |(3071882567/10000000000 : ℝ)|=(3071882567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427599379/10000000000 : ℝ)|^4691 ≤ (45761232556471/100000000000000 : ℝ)^3667
        have hw : |(5427599379/10000000000 : ℝ)|=(5427599379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_4 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-800606611/5000000000 : ℝ)*x 0 + (613128909/1250000000 : ℝ)*x 1 + (5834667991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800606611/5000000000 : ℝ)^4691 ≤ (4800248463471/50000000000000 : ℝ)^3667 := by
    have hnat : (800606611 : ℕ)^4691*50000000000000^3667 ≤ 4800248463471^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800606611 5000000000 4800248463471 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613128909/1250000000 : ℝ)^4691 ≤ (8040523322391/20000000000000 : ℝ)^3667 := by
    have hnat : (613128909 : ℕ)^4691*20000000000000^3667 ≤ 8040523322391^3667*1250000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613128909 1250000000 8040523322391 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5834667991/10000000000 : ℝ)^4691 ≤ (50196886450501/100000000000000 : ℝ)^3667 := by
    have hnat : (5834667991 : ℕ)^4691*100000000000000^3667 ≤ 50196886450501^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834667991 10000000000 50196886450501 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-800606611/5000000000 : ℝ), (613128909/1250000000 : ℝ), (5834667991/10000000000 : ℝ)] ![(4800248463471/50000000000000 : ℝ), (8040523322391/20000000000000 : ℝ), (50196886450501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-800606611/5000000000 : ℝ)|^4691 ≤ (4800248463471/50000000000000 : ℝ)^3667
        have hw : |(-800606611/5000000000 : ℝ)|=(800606611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(613128909/1250000000 : ℝ)|^4691 ≤ (8040523322391/20000000000000 : ℝ)^3667
        have hw : |(613128909/1250000000 : ℝ)|=(613128909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5834667991/10000000000 : ℝ)|^4691 ≤ (50196886450501/100000000000000 : ℝ)^3667
        have hw : |(5834667991/10000000000 : ℝ)|=(5834667991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_5 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192953107/10000000000 : ℝ)*x 0 + (-1188555411/10000000000 : ℝ)*x 1 + (5834668411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192953107/10000000000 : ℝ)^4691 ≤ (43245869057357/100000000000000 : ℝ)^3667 := by
    have hnat : (5192953107 : ℕ)^4691*100000000000000^3667 ≤ 43245869057357^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192953107 10000000000 43245869057357 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188555411/10000000000 : ℝ)^4691 ≤ (1311447970643/20000000000000 : ℝ)^3667 := by
    have hnat : (1188555411 : ℕ)^4691*20000000000000^3667 ≤ 1311447970643^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188555411 10000000000 1311447970643 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5834668411/10000000000 : ℝ)^4691 ≤ (12549222768217/25000000000000 : ℝ)^3667 := by
    have hnat : (5834668411 : ℕ)^4691*25000000000000^3667 ≤ 12549222768217^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834668411 10000000000 12549222768217 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192953107/10000000000 : ℝ), (-1188555411/10000000000 : ℝ), (5834668411/10000000000 : ℝ)] ![(43245869057357/100000000000000 : ℝ), (1311447970643/20000000000000 : ℝ), (12549222768217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192953107/10000000000 : ℝ)|^4691 ≤ (43245869057357/100000000000000 : ℝ)^3667
        have hw : |(5192953107/10000000000 : ℝ)|=(5192953107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1188555411/10000000000 : ℝ)|^4691 ≤ (1311447970643/20000000000000 : ℝ)^3667
        have hw : |(-1188555411/10000000000 : ℝ)|=(1188555411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5834668411/10000000000 : ℝ)|^4691 ≤ (12549222768217/25000000000000 : ℝ)^3667
        have hw : |(5834668411/10000000000 : ℝ)|=(5834668411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_6 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192951911/10000000000 : ℝ)*x 0 + (5834669791/10000000000 : ℝ)*x 1 + (-237711013/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192951911/10000000000 : ℝ)^4691 ≤ (43245856315993/100000000000000 : ℝ)^3667 := by
    have hnat : (5192951911 : ℕ)^4691*100000000000000^3667 ≤ 43245856315993^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192951911 10000000000 43245856315993 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5834669791/10000000000 : ℝ)^4691 ≤ (50196906260647/100000000000000 : ℝ)^3667 := by
    have hnat : (5834669791 : ℕ)^4691*100000000000000^3667 ≤ 50196906260647^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834669791 10000000000 50196906260647 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237711013/2000000000 : ℝ)^4691 ≤ (6557237411291/100000000000000 : ℝ)^3667 := by
    have hnat : (237711013 : ℕ)^4691*100000000000000^3667 ≤ 6557237411291^3667*2000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237711013 2000000000 6557237411291 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192951911/10000000000 : ℝ), (5834669791/10000000000 : ℝ), (-237711013/2000000000 : ℝ)] ![(43245856315993/100000000000000 : ℝ), (50196906260647/100000000000000 : ℝ), (6557237411291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192951911/10000000000 : ℝ)|^4691 ≤ (43245856315993/100000000000000 : ℝ)^3667
        have hw : |(5192951911/10000000000 : ℝ)|=(5192951911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5834669791/10000000000 : ℝ)|^4691 ≤ (50196906260647/100000000000000 : ℝ)^3667
        have hw : |(5834669791/10000000000 : ℝ)|=(5834669791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237711013/2000000000 : ℝ)|^4691 ≤ (6557237411291/100000000000000 : ℝ)^3667
        have hw : |(-237711013/2000000000 : ℝ)|=(237711013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s0_7 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (257844139/625000000 : ℝ)*x 0 + (5367508431/10000000000 : ℝ)*x 1 + (3134126899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257844139/625000000 : ℝ)^4691 ≤ (8054531769551/25000000000000 : ℝ)^3667 := by
    have hnat : (257844139 : ℕ)^4691*25000000000000^3667 ≤ 8054531769551^3667*625000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257844139 625000000 8054531769551 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5367508431/10000000000 : ℝ)^4691 ≤ (45114119968337/100000000000000 : ℝ)^3667 := by
    have hnat : (5367508431 : ℕ)^4691*100000000000000^3667 ≤ 45114119968337^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367508431 10000000000 45114119968337 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134126899/10000000000 : ℝ)^4691 ≤ (11333876472893/50000000000000 : ℝ)^3667 := by
    have hnat : (3134126899 : ℕ)^4691*50000000000000^3667 ≤ 11333876472893^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134126899 10000000000 11333876472893 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257844139/625000000 : ℝ), (5367508431/10000000000 : ℝ), (3134126899/10000000000 : ℝ)] ![(8054531769551/25000000000000 : ℝ), (45114119968337/100000000000000 : ℝ), (11333876472893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257844139/625000000 : ℝ)|^4691 ≤ (8054531769551/25000000000000 : ℝ)^3667
        have hw : |(257844139/625000000 : ℝ)|=(257844139/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5367508431/10000000000 : ℝ)|^4691 ≤ (45114119968337/100000000000000 : ℝ)^3667
        have hw : |(5367508431/10000000000 : ℝ)|=(5367508431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134126899/10000000000 : ℝ)|^4691 ≤ (11333876472893/50000000000000 : ℝ)^3667
        have hw : |(3134126899/10000000000 : ℝ)|=(3134126899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1593_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3643/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (154/625 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4687/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4687 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4687*1^1024 ≤ 0^1024*1^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4687/1024 : ℝ) ≤ (188573005991559753/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4687 ≤ (188573005991559753/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4687*12500000000000000000^1024 ≤ 188573005991559753^1024*5^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 188573005991559753 12500000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (188573005991559753/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4687 := by
      have hnat : (1 : ℕ)^1024*1^4687 ≤ 1^4687*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12688573005991559753/12500000000000000000 : ℝ) ≤ (2006553293414249/2000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (12688573005991559753/12500000000000000000 : ℝ)^1024 ≤ (2006553293414249/2000000000000000 : ℝ)^4687 := by
      have hnat : (12688573005991559753 : ℕ)^1024*2000000000000000^4687 ≤ 2006553293414249^4687*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12688573005991559753 12500000000000000000 2006553293414249 2000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006553293414249/2000000000000000 : ℝ)) (X := (12688573005991559753/12500000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6438573005991559753/6250000000000000000 : ℝ) ≤ (1006553293414249/1000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (6438573005991559753/6250000000000000000 : ℝ)^1024 ≤ (1006553293414249/1000000000000000 : ℝ)^4687 := by
      have hnat : (6438573005991559753 : ℕ)^1024*1000000000000000^4687 ≤ 1006553293414249^4687*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6438573005991559753 6250000000000000000 1006553293414249 1000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006553293414249/1000000000000000 : ℝ)) (X := (6438573005991559753/6250000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6553293414249/800000000000000 : ℝ)*(0 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6553293414249/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(188573005991559753/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6553293414249/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4687/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6553293414249/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2006553293414249/2000000000000000 : ℝ) by norm_num, show 1+(188573005991559753/12500000000000000000 : ℝ)+(0 : ℝ)=(12688573005991559753/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(188573005991559753/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6553293414249/800000000000000 : ℝ)*(2/5 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6553293414249/800000000000000 : ℝ)*(2/5 : ℝ)=(1006553293414249/1000000000000000 : ℝ) by norm_num, show 1+2*(188573005991559753/12500000000000000000 : ℝ)=(6438573005991559753/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6553293414249/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6553293414249/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6553293414249/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6553293414249/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6553293414249/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6553293414249/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-199772151/1250000000 : ℝ)*X 0 0+(5860577829/10000000000 : ℝ)*X 0 1+(4880020459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5460777209/10000000000 : ℝ)*X 1 0+(-2143202881/10000000000 : ℝ)*X 1 1+(4880020327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5460777237/10000000000 : ℝ)*X 2 0+(4880020247/10000000000 : ℝ)*X 2 1+(-428640589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4118215503/10000000000 : ℝ)*X 0 0+(3071882567/10000000000 : ℝ)*X 0 1+(5427599379/10000000000 : ℝ)*X 0 2+(4118215503/10000000000 : ℝ)*X 1 0+(3071882567/10000000000 : ℝ)*X 1 1+(5427599379/10000000000 : ℝ)*X 1 2+(4118215503/10000000000 : ℝ)*X 2 0+(3071882567/10000000000 : ℝ)*X 2 1+(5427599379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-800606611/5000000000 : ℝ)*X 0 0+(613128909/1250000000 : ℝ)*X 0 1+(5834667991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5192953107/10000000000 : ℝ)*X 1 0+(-1188555411/10000000000 : ℝ)*X 1 1+(5834668411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5192951911/10000000000 : ℝ)*X 2 0+(5834669791/10000000000 : ℝ)*X 2 1+(-237711013/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((257844139/625000000 : ℝ)*X 0 0+(5367508431/10000000000 : ℝ)*X 0 1+(3134126899/10000000000 : ℝ)*X 0 2+(257844139/625000000 : ℝ)*X 1 0+(5367508431/10000000000 : ℝ)*X 1 1+(3134126899/10000000000 : ℝ)*X 1 2+(257844139/625000000 : ℝ)*X 2 0+(5367508431/10000000000 : ℝ)*X 2 1+(3134126899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79026974781553482938109/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33127827/50000000000000 : ℝ)*(base1) + (308967879/20000000000000 : ℝ)*(base19) + (775034293/50000000000000 : ℝ)*(base23) + (211019283/100000000000000 : ℝ)*(upper3) + (96436639/50000000000000 : ℝ)*(upper5) + (722171697162953/100000000000000 : ℝ)*(major0) + (722171697162953/100000000000000 : ℝ)*(major1) + (722171697162953/100000000000000 : ℝ)*(major2) + (101983357497243/10000000000000 : ℝ)*(sp0) + (1019837559037459/100000000000000 : ℝ)*(sp1) + (254959388452067/25000000000000 : ℝ)*(sp2) + (424501510496987/100000000000000 : ℝ)*(sp3) + (5595160077/100000000000000 : ℝ)*(sp4) + (612568289/25000000000000 : ℝ)*(sp7) + (424504027025797/100000000000000 : ℝ)*(f.failure) + (509919551938427/50000000000000 : ℝ)*(f.sum) + (70212330277297/40000000000000000000000000000 : ℝ)*base65 + (200773382797297/80000000000000000000000000000 : ℝ)*base67 + (659633485597297/80000000000000000000000000000 : ℝ)*base69 + (382269538237297/80000000000000000000000000000 : ℝ)*base71 + (6411094322703/40000000000000000000000000000 : ℝ)*base74 + (25994412317297/80000000000000000000000000000 : ℝ)*base75 + (24483651437297/80000000000000000000000000000 : ℝ)*base77 + (383107800237297/80000000000000000000000000000 : ℝ)*base79 + (171258482837297/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (40262449/10000000000000000000000 : ℝ)*base90 + (40262449/10000000000000000000000 : ℝ)*base92 + (40262449/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14725743216773384178441/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67935807/20000000000000 : ℝ)*(base19) + (31969403/4000000000000 : ℝ)*(base23) + (812180679/100000000000000 : ℝ)*(base39) + (21109/1250000000000 : ℝ)*(upper2) + (8917329/1562500000000 : ℝ)*(upper5) + (380858779673397/50000000000000 : ℝ)*(major0) + (380858779673397/50000000000000 : ℝ)*(major1) + (152343349433223/20000000000000 : ℝ)*(major2) + (977670913/50000000000000 : ℝ)*(sp1) + (53554943/50000000000000 : ℝ)*(sp2) + (1075684567228669/100000000000000 : ℝ)*(sp4) + (16807535503247/1562500000000 : ℝ)*(sp5) + (1075684473064387/100000000000000 : ℝ)*(sp6) + (111937428685333/25000000000000 : ℝ)*(sp7) + (111937428685333/25000000000000 : ℝ)*(f.failure) + (268921344852337/25000000000000 : ℝ)*(f.sum) + (277734895040341/80000000000000000000000000000 : ℝ)*base65 + (102613010765473/16000000000000000000000000000 : ℝ)*base68 + (21862308153853/40000000000000000000000000000 : ℝ)*base69 + (10499846866527/16000000000000000000000000000 : ℝ)*base71 + (325507620799659/80000000000000000000000000000 : ℝ)*base74 + (181602340286147/40000000000000000000000000000 : ℝ)*base76 + (41858889753853/40000000000000000000000000000 : ℝ)*base77 + (170727356006147/40000000000000000000000000000 : ℝ)*base80 + (1577145173853/20000000000000000000000000000 : ℝ)*base81 + (3242239/2500000000000000000000 : ℝ)*base89 + (3242239/2500000000000000000000 : ℝ)*base91 + (3242239/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1593_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3643/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (154/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1593_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1593_s1_0 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-108102289/625000000 : ℝ)*x 0 + (554663177/1000000000 : ℝ)*x 1 + (2554554963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108102289/625000000 : ℝ)^4691 ≤ (5298168927797/50000000000000 : ℝ)^3667 := by
    have hnat : (108102289 : ℕ)^4691*50000000000000^3667 ≤ 5298168927797^3667*625000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108102289 625000000 5298168927797 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554663177/1000000000 : ℝ)^4691 ≤ (4704897942217/10000000000000 : ℝ)^3667 := by
    have hnat : (554663177 : ℕ)^4691*10000000000000^3667 ≤ 4704897942217^3667*1000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554663177 1000000000 4704897942217 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2554554963/5000000000 : ℝ)^4691 ≤ (42354682702227/100000000000000 : ℝ)^3667 := by
    have hnat : (2554554963 : ℕ)^4691*100000000000000^3667 ≤ 42354682702227^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554554963 5000000000 42354682702227 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108102289/625000000 : ℝ), (554663177/1000000000 : ℝ), (2554554963/5000000000 : ℝ)] ![(5298168927797/50000000000000 : ℝ), (4704897942217/10000000000000 : ℝ), (42354682702227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108102289/625000000 : ℝ)|^4691 ≤ (5298168927797/50000000000000 : ℝ)^3667
        have hw : |(-108102289/625000000 : ℝ)|=(108102289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554663177/1000000000 : ℝ)|^4691 ≤ (4704897942217/10000000000000 : ℝ)^3667
        have hw : |(554663177/1000000000 : ℝ)|=(554663177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2554554963/5000000000 : ℝ)|^4691 ≤ (42354682702227/100000000000000 : ℝ)^3667
        have hw : |(2554554963/5000000000 : ℝ)|=(2554554963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_1 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377163021/10000000000 : ℝ)*x 0 + (-489787143/2500000000 : ℝ)*x 1 + (2554554893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377163021/10000000000 : ℝ)^4691 ≤ (9043590675919/20000000000000 : ℝ)^3667 := by
    have hnat : (5377163021 : ℕ)^4691*20000000000000^3667 ≤ 9043590675919^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377163021 10000000000 9043590675919 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489787143/2500000000 : ℝ)^4691 ≤ (12427365395517/100000000000000 : ℝ)^3667 := by
    have hnat : (489787143 : ℕ)^4691*100000000000000^3667 ≤ 12427365395517^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489787143 2500000000 12427365395517 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2554554893/5000000000 : ℝ)^4691 ≤ (42354681217527/100000000000000 : ℝ)^3667 := by
    have hnat : (2554554893 : ℕ)^4691*100000000000000^3667 ≤ 42354681217527^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554554893 5000000000 42354681217527 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377163021/10000000000 : ℝ), (-489787143/2500000000 : ℝ), (2554554893/5000000000 : ℝ)] ![(9043590675919/20000000000000 : ℝ), (12427365395517/100000000000000 : ℝ), (42354681217527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377163021/10000000000 : ℝ)|^4691 ≤ (9043590675919/20000000000000 : ℝ)^3667
        have hw : |(5377163021/10000000000 : ℝ)|=(5377163021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489787143/2500000000 : ℝ)|^4691 ≤ (12427365395517/100000000000000 : ℝ)^3667
        have hw : |(-489787143/2500000000 : ℝ)|=(489787143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2554554893/5000000000 : ℝ)|^4691 ≤ (42354681217527/100000000000000 : ℝ)^3667
        have hw : |(2554554893/5000000000 : ℝ)|=(2554554893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_2 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344290689/2500000000 : ℝ)*x 0 + (1277277501/2500000000 : ℝ)*x 1 + (-979574319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344290689/2500000000 : ℝ)^4691 ≤ (11304487632213/25000000000000 : ℝ)^3667 := by
    have hnat : (1344290689 : ℕ)^4691*25000000000000^3667 ≤ 11304487632213^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344290689 2500000000 11304487632213 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1277277501/2500000000 : ℝ)^4691 ≤ (42354683529417/100000000000000 : ℝ)^3667 := by
    have hnat : (1277277501 : ℕ)^4691*100000000000000^3667 ≤ 42354683529417^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277277501 2500000000 42354683529417 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979574319/5000000000 : ℝ)^4691 ≤ (310684148277/2500000000000 : ℝ)^3667 := by
    have hnat : (979574319 : ℕ)^4691*2500000000000^3667 ≤ 310684148277^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979574319 5000000000 310684148277 2500000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344290689/2500000000 : ℝ), (1277277501/2500000000 : ℝ), (-979574319/5000000000 : ℝ)] ![(11304487632213/25000000000000 : ℝ), (42354683529417/100000000000000 : ℝ), (310684148277/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344290689/2500000000 : ℝ)|^4691 ≤ (11304487632213/25000000000000 : ℝ)^3667
        have hw : |(1344290689/2500000000 : ℝ)|=(1344290689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1277277501/2500000000 : ℝ)|^4691 ≤ (42354683529417/100000000000000 : ℝ)^3667
        have hw : |(1277277501/2500000000 : ℝ)|=(1277277501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979574319/5000000000 : ℝ)|^4691 ≤ (310684148277/2500000000000 : ℝ)^3667
        have hw : |(-979574319/5000000000 : ℝ)|=(979574319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_3 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4213418273/10000000000 : ℝ)*x 0 + (3713690637/10000000000 : ℝ)*x 1 + (2382402279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4213418273/10000000000 : ℝ)^4691 ≤ (3309899271713/10000000000000 : ℝ)^3667 := by
    have hnat : (4213418273 : ℕ)^4691*10000000000000^3667 ≤ 3309899271713^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213418273 10000000000 3309899271713 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3713690637/10000000000 : ℝ)^4691 ≤ (28162753542531/100000000000000 : ℝ)^3667 := by
    have hnat : (3713690637 : ℕ)^4691*100000000000000^3667 ≤ 28162753542531^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713690637 10000000000 28162753542531 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2382402279/5000000000 : ℝ)^4691 ≤ (38738253726257/100000000000000 : ℝ)^3667 := by
    have hnat : (2382402279 : ℕ)^4691*100000000000000^3667 ≤ 38738253726257^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382402279 5000000000 38738253726257 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4213418273/10000000000 : ℝ), (3713690637/10000000000 : ℝ), (2382402279/5000000000 : ℝ)] ![(3309899271713/10000000000000 : ℝ), (28162753542531/100000000000000 : ℝ), (38738253726257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4213418273/10000000000 : ℝ)|^4691 ≤ (3309899271713/10000000000000 : ℝ)^3667
        have hw : |(4213418273/10000000000 : ℝ)|=(4213418273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3713690637/10000000000 : ℝ)|^4691 ≤ (28162753542531/100000000000000 : ℝ)^3667
        have hw : |(3713690637/10000000000 : ℝ)|=(3713690637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2382402279/5000000000 : ℝ)|^4691 ≤ (38738253726257/100000000000000 : ℝ)^3667
        have hw : |(2382402279/5000000000 : ℝ)|=(2382402279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_4 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-864949439/5000000000 : ℝ)*x 0 + (5114031851/10000000000 : ℝ)*x 1 + (13854077/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864949439/5000000000 : ℝ)^4691 ≤ (10598393210207/100000000000000 : ℝ)^3667 := by
    have hnat : (864949439 : ℕ)^4691*100000000000000^3667 ≤ 10598393210207^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864949439 5000000000 10598393210207 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5114031851/10000000000 : ℝ)^4691 ≤ (42406886740459/100000000000000 : ℝ)^3667 := by
    have hnat : (5114031851 : ℕ)^4691*100000000000000^3667 ≤ 42406886740459^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5114031851 10000000000 42406886740459 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13854077/25000000 : ℝ)^4691 ≤ (46994720025931/100000000000000 : ℝ)^3667 := by
    have hnat : (13854077 : ℕ)^4691*100000000000000^3667 ≤ 46994720025931^3667*25000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13854077 25000000 46994720025931 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-864949439/5000000000 : ℝ), (5114031851/10000000000 : ℝ), (13854077/25000000 : ℝ)] ![(10598393210207/100000000000000 : ℝ), (42406886740459/100000000000000 : ℝ), (46994720025931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-864949439/5000000000 : ℝ)|^4691 ≤ (10598393210207/100000000000000 : ℝ)^3667
        have hw : |(-864949439/5000000000 : ℝ)|=(864949439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5114031851/10000000000 : ℝ)|^4691 ≤ (42406886740459/100000000000000 : ℝ)^3667
        have hw : |(5114031851/10000000000 : ℝ)|=(5114031851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13854077/25000000 : ℝ)|^4691 ≤ (46994720025931/100000000000000 : ℝ)^3667
        have hw : |(13854077/25000000 : ℝ)|=(13854077/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_5 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52610899/100000000 : ℝ)*x 0 + (-381657727/2500000000 : ℝ)*x 1 + (1385407563/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52610899/100000000 : ℝ)^4691 ≤ (43973077398333/100000000000000 : ℝ)^3667 := by
    have hnat : (52610899 : ℕ)^4691*100000000000000^3667 ≤ 43973077398333^3667*100000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52610899 100000000 43973077398333 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (381657727/2500000000 : ℝ)^4691 ≤ (1806441702161/20000000000000 : ℝ)^3667 := by
    have hnat : (381657727 : ℕ)^4691*20000000000000^3667 ≤ 1806441702161^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381657727 2500000000 1806441702161 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385407563/2500000000 : ℝ)^4691 ≤ (11748678520251/25000000000000 : ℝ)^3667 := by
    have hnat : (1385407563 : ℕ)^4691*25000000000000^3667 ≤ 11748678520251^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385407563 2500000000 11748678520251 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52610899/100000000 : ℝ), (-381657727/2500000000 : ℝ), (1385407563/2500000000 : ℝ)] ![(43973077398333/100000000000000 : ℝ), (1806441702161/20000000000000 : ℝ), (11748678520251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52610899/100000000 : ℝ)|^4691 ≤ (43973077398333/100000000000000 : ℝ)^3667
        have hw : |(52610899/100000000 : ℝ)|=(52610899/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-381657727/2500000000 : ℝ)|^4691 ≤ (1806441702161/20000000000000 : ℝ)^3667
        have hw : |(-381657727/2500000000 : ℝ)|=(381657727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1385407563/2500000000 : ℝ)|^4691 ≤ (11748678520251/25000000000000 : ℝ)^3667
        have hw : |(1385407563/2500000000 : ℝ)|=(1385407563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_6 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261092623/10000000000 : ℝ)*x 0 + (2770814687/5000000000 : ℝ)*x 1 + (-1526628319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261092623/10000000000 : ℝ)^4691 ≤ (43973106513101/100000000000000 : ℝ)^3667 := by
    have hnat : (5261092623 : ℕ)^4691*100000000000000^3667 ≤ 43973106513101^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261092623 10000000000 43973106513101 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2770814687/5000000000 : ℝ)^4691 ≤ (23497352278051/50000000000000 : ℝ)^3667 := by
    have hnat : (2770814687 : ℕ)^4691*50000000000000^3667 ≤ 23497352278051^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2770814687 5000000000 23497352278051 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1526628319/10000000000 : ℝ)^4691 ≤ (1806437783151/20000000000000 : ℝ)^3667 := by
    have hnat : (1526628319 : ℕ)^4691*20000000000000^3667 ≤ 1806437783151^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526628319 10000000000 1806437783151 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261092623/10000000000 : ℝ), (2770814687/5000000000 : ℝ), (-1526628319/10000000000 : ℝ)] ![(43973106513101/100000000000000 : ℝ), (23497352278051/50000000000000 : ℝ), (1806437783151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261092623/10000000000 : ℝ)|^4691 ≤ (43973106513101/100000000000000 : ℝ)^3667
        have hw : |(5261092623/10000000000 : ℝ)|=(5261092623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2770814687/5000000000 : ℝ)|^4691 ≤ (23497352278051/50000000000000 : ℝ)^3667
        have hw : |(2770814687/5000000000 : ℝ)|=(2770814687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1526628319/10000000000 : ℝ)|^4691 ≤ (1806437783151/20000000000000 : ℝ)^3667
        have hw : |(-1526628319/10000000000 : ℝ)|=(1526628319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s1_7 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52675609/125000000 : ℝ)*x 0 + (1188244697/2500000000 : ℝ)*x 1 + (3725705857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52675609/125000000 : ℝ)^4691 ≤ (2069083024043/6250000000000 : ℝ)^3667 := by
    have hnat : (52675609 : ℕ)^4691*6250000000000^3667 ≤ 2069083024043^3667*125000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52675609 125000000 2069083024043 6250000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1188244697/2500000000 : ℝ)^4691 ≤ (38615303796189/100000000000000 : ℝ)^3667 := by
    have hnat : (1188244697 : ℕ)^4691*100000000000000^3667 ≤ 38615303796189^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188244697 2500000000 38615303796189 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3725705857/10000000000 : ℝ)^4691 ≤ (1767460487179/6250000000000 : ℝ)^3667 := by
    have hnat : (3725705857 : ℕ)^4691*6250000000000^3667 ≤ 1767460487179^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725705857 10000000000 1767460487179 6250000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52675609/125000000 : ℝ), (1188244697/2500000000 : ℝ), (3725705857/10000000000 : ℝ)] ![(2069083024043/6250000000000 : ℝ), (38615303796189/100000000000000 : ℝ), (1767460487179/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52675609/125000000 : ℝ)|^4691 ≤ (2069083024043/6250000000000 : ℝ)^3667
        have hw : |(52675609/125000000 : ℝ)|=(52675609/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1188244697/2500000000 : ℝ)|^4691 ≤ (38615303796189/100000000000000 : ℝ)^3667
        have hw : |(1188244697/2500000000 : ℝ)|=(1188244697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3725705857/10000000000 : ℝ)|^4691 ≤ (1767460487179/6250000000000 : ℝ)^3667
        have hw : |(3725705857/10000000000 : ℝ)|=(3725705857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1593_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (154/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3643/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1101/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (154/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3643/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (154/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3643/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (154/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3643/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (154/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3643/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (154/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3643/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (154/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3643/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3643/100000 : ℝ) ^ (4687/1024 : ℝ) ≤ (13018324648861/50000000000000000000 : ℝ) := by
    have hpowers : (3643/100000 : ℝ)^4687 ≤ (13018324648861/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3643 : ℕ)^4687*50000000000000000000^1024 ≤ 13018324648861^1024*100000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3643 100000 13018324648861 50000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3643/100000 : ℝ)) (X := (13018324648861/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (154/625 : ℝ) ^ (4687/1024 : ℝ) ≤ (8211437674260473/5000000000000000000 : ℝ) := by
    have hpowers : (154/625 : ℝ)^4687 ≤ (8211437674260473/5000000000000000000 : ℝ)^1024 := by
      have hnat : (154 : ℕ)^4687*5000000000000000000^1024 ≤ 8211437674260473^1024*625^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154 625 8211437674260473 5000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (154/625 : ℝ)) (X := (8211437674260473/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013018324648861/25000000000000000000 : ℝ) ≤ (10000001137679687/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (25000013018324648861/25000000000000000000 : ℝ)^1024 ≤ (10000001137679687/10000000000000000 : ℝ)^4687 := by
      have hnat : (25000013018324648861 : ℕ)^1024*10000000000000000^4687 ≤ 10000001137679687^4687*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013018324648861 25000000000000000000 10000001137679687 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001137679687/10000000000000000 : ℝ)) (X := (25000013018324648861/25000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50082127395067253591/50000000000000000000 : ℝ) ≤ (10003586282354899/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (50082127395067253591/50000000000000000000 : ℝ)^1024 ≤ (10003586282354899/10000000000000000 : ℝ)^4687 := by
      have hnat : (50082127395067253591 : ℕ)^1024*10000000000000000^4687 ≤ 10003586282354899^4687*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50082127395067253591 50000000000000000000 10003586282354899 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003586282354899/10000000000000000 : ℝ)) (X := (50082127395067253591/50000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2508211437674260473/2500000000000000000 : ℝ) ≤ (10007171427030111/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (2508211437674260473/2500000000000000000 : ℝ)^1024 ≤ (10007171427030111/10000000000000000 : ℝ)^4687 := by
      have hnat : (2508211437674260473 : ℕ)^1024*10000000000000000^4687 ≤ 10007171427030111^4687*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2508211437674260473 2500000000000000000 10007171427030111 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007171427030111/10000000000000000 : ℝ)) (X := (2508211437674260473/2500000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13018324648861/50000000000000000000 : ℝ) ≤ ((209943902523756793307/209970000000000000000 : ℝ)+2*(896286168803/524925000000000 : ℝ)*(3643/100000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (209943902523756793307/209970000000000000000 : ℝ)+2*(896286168803/524925000000000 : ℝ)*(3643/100000 : ℝ)=(10000001137679687/10000000000000000 : ℝ) by norm_num, show 1+2*(13018324648861/50000000000000000000 : ℝ)=(25000013018324648861/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8211437674260473/5000000000000000000 : ℝ)+(13018324648861/50000000000000000000 : ℝ) ≤ ((209943902523756793307/209970000000000000000 : ℝ)+(896286168803/524925000000000 : ℝ)*((154/625 : ℝ)+(3643/100000 : ℝ)))^(4687/1024 : ℝ) := by
    rw [show (209943902523756793307/209970000000000000000 : ℝ)+(896286168803/524925000000000 : ℝ)*((154/625 : ℝ)+(3643/100000 : ℝ))=(10003586282354899/10000000000000000 : ℝ) by norm_num, show 1+(8211437674260473/5000000000000000000 : ℝ)+(13018324648861/50000000000000000000 : ℝ)=(50082127395067253591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8211437674260473/5000000000000000000 : ℝ) ≤ ((209943902523756793307/209970000000000000000 : ℝ)+2*(896286168803/524925000000000 : ℝ)*(154/625 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (209943902523756793307/209970000000000000000 : ℝ)+2*(896286168803/524925000000000 : ℝ)*(154/625 : ℝ)=(10007171427030111/10000000000000000 : ℝ) by norm_num, show 1+2*(8211437674260473/5000000000000000000 : ℝ)=(2508211437674260473/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (209943902523756793307/209970000000000000000 : ℝ)*(X 1 0+X 2 0)+(896286168803/524925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (3643/100000 : ℝ)) (hi := (154/625 : ℝ)) (c := (209943902523756793307/209970000000000000000 : ℝ)) (alpha := (896286168803/524925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (209943902523756793307/209970000000000000000 : ℝ)*(X 0 1+X 2 1)+(896286168803/524925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (3643/100000 : ℝ)) (hi := (154/625 : ℝ)) (c := (209943902523756793307/209970000000000000000 : ℝ)) (alpha := (896286168803/524925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (209943902523756793307/209970000000000000000 : ℝ)*(X 0 2+X 1 2)+(896286168803/524925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (3643/100000 : ℝ)) (hi := (154/625 : ℝ)) (c := (209943902523756793307/209970000000000000000 : ℝ)) (alpha := (896286168803/524925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-108102289/625000000 : ℝ)*X 0 0+(554663177/1000000000 : ℝ)*X 0 1+(2554554963/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377163021/10000000000 : ℝ)*X 1 0+(-489787143/2500000000 : ℝ)*X 1 1+(2554554893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344290689/2500000000 : ℝ)*X 2 0+(1277277501/2500000000 : ℝ)*X 2 1+(-979574319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4213418273/10000000000 : ℝ)*X 0 0+(3713690637/10000000000 : ℝ)*X 0 1+(2382402279/5000000000 : ℝ)*X 0 2+(4213418273/10000000000 : ℝ)*X 1 0+(3713690637/10000000000 : ℝ)*X 1 1+(2382402279/5000000000 : ℝ)*X 1 2+(4213418273/10000000000 : ℝ)*X 2 0+(3713690637/10000000000 : ℝ)*X 2 1+(2382402279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-864949439/5000000000 : ℝ)*X 0 0+(5114031851/10000000000 : ℝ)*X 0 1+(13854077/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52610899/100000000 : ℝ)*X 1 0+(-381657727/2500000000 : ℝ)*X 1 1+(1385407563/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261092623/10000000000 : ℝ)*X 2 0+(2770814687/5000000000 : ℝ)*X 2 1+(-1526628319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52675609/125000000 : ℝ)*X 0 0+(1188244697/2500000000 : ℝ)*X 0 1+(3725705857/10000000000 : ℝ)*X 0 2+(52675609/125000000 : ℝ)*X 1 0+(1188244697/2500000000 : ℝ)*X 1 1+(3725705857/10000000000 : ℝ)*X 1 2+(52675609/125000000 : ℝ)*X 2 0+(1188244697/2500000000 : ℝ)*X 2 1+(3725705857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24026618581016409625725846047/3499500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59464719/100000000000000 : ℝ)*(base1) + (154665583/10000000000000 : ℝ)*(base19) + (1434014633/100000000000000 : ℝ)*(base23) + (188535223/100000000000000 : ℝ)*(upper3) + (132247819/100000000000000 : ℝ)*(upper5) + (1618503324954607/100000000000000 : ℝ)*(major0) + (1618503324954607/100000000000000 : ℝ)*(major1) + (1618503324954607/100000000000000 : ℝ)*(major2) + (1142806378449433/50000000000000 : ℝ)*(sp0) + (1142811419468301/50000000000000 : ℝ)*(sp1) + (11428114757889/500000000000 : ℝ)*(sp2) + (951376668754193/100000000000000 : ℝ)*(sp3) + (2337631657/20000000000000 : ℝ)*(sp4) + (5307240231/100000000000000 : ℝ)*(sp7) + (475691017729571/50000000000000 : ℝ)*(f.failure) + (142851524099527/6250000000000 : ℝ)*(f.sum) + (358867072617391/104985000000000000000000000000 : ℝ)*base66 + (176555657882203184651/20997000000000000000000000000000000 : ℝ)*base68 + (106483361953444184651/20997000000000000000000000000000000 : ℝ)*base70 + (138876506254222184651/20997000000000000000000000000000000 : ℝ)*base72 + (490195772843941/104985000000000000000000000000 : ℝ)*base74 + (31353266733676184651/20997000000000000000000000000000000 : ℝ)*base76 + (188400495705748184651/20997000000000000000000000000000000 : ℝ)*base78 + (170512781018668184651/20997000000000000000000000000000000 : ℝ)*base80 + (207457936320599/104985000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15559593/5000000000000000000000 : ℝ)*base89 + (15559593/5000000000000000000000 : ℝ)*base91 + (15559593/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12107848334304676453770170669/1749750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26904241/10000000000000 : ℝ)*(base19) + (780993987/50000000000000 : ℝ)*(base23) + (4655629/6250000000000 : ℝ)*(lower2) + (395385293/100000000000000 : ℝ)*(upper5) + (828026420611367/50000000000000 : ℝ)*(major0) + (828026420611367/50000000000000 : ℝ)*(major1) + (828026420611367/50000000000000 : ℝ)*(major2) + (189795051/100000000000000 : ℝ)*(sp0) + (10158172929/100000000000000 : ℝ)*(sp2) + (844019693/50000000000000 : ℝ)*(sp3) + (1169325511373021/50000000000000 : ℝ)*(sp4) + (584662735874671/25000000000000 : ℝ)*(sp5) + (2338639492380191/100000000000000 : ℝ)*(sp6) + (973452551206349/100000000000000 : ℝ)*(sp7) + (194690847849147/20000000000000 : ℝ)*(f.failure) + (1169325606270547/50000000000000 : ℝ)*(f.sum) + (195962433551989/52492500000000000000000000000 : ℝ)*base65 + (68003656972733120669/10498500000000000000000000000000000 : ℝ)*base67 + (28233560516334620669/10498500000000000000000000000000000 : ℝ)*base69 + (73673677712238879331/10498500000000000000000000000000000 : ℝ)*base72 + (277089914395969/52492500000000000000000000000 : ℝ)*base73 + (14616261896852379331/10498500000000000000000000000000000 : ℝ)*base76 + (3879352783163379331/10498500000000000000000000000000000 : ℝ)*base78 + (95769353989059879331/10498500000000000000000000000000000 : ℝ)*base80 + (65254906893679/52492500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1904399/2000000000000000000000 : ℝ)*base90 + (1904399/2000000000000000000000 : ℝ)*base92 + (1904399/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1593_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (154/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3643/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1101/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1593_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1593_s2_0 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-873033421/5000000000 : ℝ)*x 0 + (684304639/1250000000 : ℝ)*x 1 + (5170584551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873033421/5000000000 : ℝ)^4691 ≤ (2681318382511/25000000000000 : ℝ)^3667 := by
    have hnat : (873033421 : ℕ)^4691*25000000000000^3667 ≤ 2681318382511^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873033421 5000000000 2681318382511 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684304639/1250000000 : ℝ)^4691 ≤ (2891688324739/6250000000000 : ℝ)^3667 := by
    have hnat : (684304639 : ℕ)^4691*6250000000000^3667 ≤ 2891688324739^3667*1250000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684304639 1250000000 2891688324739 6250000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170584551/10000000000 : ℝ)^4691 ≤ (43007713261863/100000000000000 : ℝ)^3667 := by
    have hnat : (5170584551 : ℕ)^4691*100000000000000^3667 ≤ 43007713261863^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170584551 10000000000 43007713261863 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-873033421/5000000000 : ℝ), (684304639/1250000000 : ℝ), (5170584551/10000000000 : ℝ)] ![(2681318382511/25000000000000 : ℝ), (2891688324739/6250000000000 : ℝ), (43007713261863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-873033421/5000000000 : ℝ)|^4691 ≤ (2681318382511/25000000000000 : ℝ)^3667
        have hw : |(-873033421/5000000000 : ℝ)|=(873033421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684304639/1250000000 : ℝ)|^4691 ≤ (2891688324739/6250000000000 : ℝ)^3667
        have hw : |(684304639/1250000000 : ℝ)|=(684304639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170584551/10000000000 : ℝ)|^4691 ≤ (43007713261863/100000000000000 : ℝ)^3667
        have hw : |(5170584551/10000000000 : ℝ)|=(5170584551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_1 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358498347/10000000000 : ℝ)*x 0 + (-951589631/5000000000 : ℝ)*x 1 + (2585292259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358498347/10000000000 : ℝ)^4691 ≤ (45017265139943/100000000000000 : ℝ)^3667 := by
    have hnat : (5358498347 : ℕ)^4691*100000000000000^3667 ≤ 45017265139943^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358498347 10000000000 45017265139943 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (951589631/5000000000 : ℝ)^4691 ≤ (11975021941681/100000000000000 : ℝ)^3667 := by
    have hnat : (951589631 : ℕ)^4691*100000000000000^3667 ≤ 11975021941681^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951589631 5000000000 11975021941681 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2585292259/5000000000 : ℝ)^4691 ≤ (43007712910727/100000000000000 : ℝ)^3667 := by
    have hnat : (2585292259 : ℕ)^4691*100000000000000^3667 ≤ 43007712910727^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585292259 5000000000 43007712910727 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358498347/10000000000 : ℝ), (-951589631/5000000000 : ℝ), (2585292259/5000000000 : ℝ)] ![(45017265139943/100000000000000 : ℝ), (11975021941681/100000000000000 : ℝ), (43007712910727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358498347/10000000000 : ℝ)|^4691 ≤ (45017265139943/100000000000000 : ℝ)^3667
        have hw : |(5358498347/10000000000 : ℝ)|=(5358498347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-951589631/5000000000 : ℝ)|^4691 ≤ (11975021941681/100000000000000 : ℝ)^3667
        have hw : |(-951589631/5000000000 : ℝ)|=(951589631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2585292259/5000000000 : ℝ)|^4691 ≤ (43007712910727/100000000000000 : ℝ)^3667
        have hw : |(2585292259/5000000000 : ℝ)|=(2585292259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_2 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358498067/10000000000 : ℝ)*x 0 + (2585292463/5000000000 : ℝ)*x 1 + (-1903179097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358498067/10000000000 : ℝ)^4691 ≤ (1125431553269/2500000000000 : ℝ)^3667 := by
    have hnat : (5358498067 : ℕ)^4691*2500000000000^3667 ≤ 1125431553269^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358498067 10000000000 1125431553269 2500000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585292463/5000000000 : ℝ)^4691 ≤ (43007717252043/100000000000000 : ℝ)^3667 := by
    have hnat : (2585292463 : ℕ)^4691*100000000000000^3667 ≤ 43007717252043^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585292463 5000000000 43007717252043 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1903179097/10000000000 : ℝ)^4691 ≤ (187109697087/1562500000000 : ℝ)^3667 := by
    have hnat : (1903179097 : ℕ)^4691*1562500000000^3667 ≤ 187109697087^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903179097 10000000000 187109697087 1562500000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358498067/10000000000 : ℝ), (2585292463/5000000000 : ℝ), (-1903179097/10000000000 : ℝ)] ![(1125431553269/2500000000000 : ℝ), (43007717252043/100000000000000 : ℝ), (187109697087/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358498067/10000000000 : ℝ)|^4691 ≤ (1125431553269/2500000000000 : ℝ)^3667
        have hw : |(5358498067/10000000000 : ℝ)|=(5358498067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585292463/5000000000 : ℝ)|^4691 ≤ (43007717252043/100000000000000 : ℝ)^3667
        have hw : |(2585292463/5000000000 : ℝ)|=(2585292463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1903179097/10000000000 : ℝ)|^4691 ≤ (187109697087/1562500000000 : ℝ)^3667
        have hw : |(-1903179097/10000000000 : ℝ)|=(1903179097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_3 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52818543/125000000 : ℝ)*x 0 + (1936475603/5000000000 : ℝ)*x 1 + (1150733487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52818543/125000000 : ℝ)^4691 ≤ (3322028733943/10000000000000 : ℝ)^3667 := by
    have hnat : (52818543 : ℕ)^4691*10000000000000^3667 ≤ 3322028733943^3667*125000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52818543 125000000 3322028733943 10000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936475603/5000000000 : ℝ)^4691 ≤ (742923104907/2500000000000 : ℝ)^3667 := by
    have hnat : (1936475603 : ℕ)^4691*2500000000000^3667 ≤ 742923104907^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936475603 5000000000 742923104907 2500000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1150733487/2500000000 : ℝ)^4691 ≤ (1853139422387/5000000000000 : ℝ)^3667 := by
    have hnat : (1150733487 : ℕ)^4691*5000000000000^3667 ≤ 1853139422387^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150733487 2500000000 1853139422387 5000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52818543/125000000 : ℝ), (1936475603/5000000000 : ℝ), (1150733487/2500000000 : ℝ)] ![(3322028733943/10000000000000 : ℝ), (742923104907/2500000000000 : ℝ), (1853139422387/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52818543/125000000 : ℝ)|^4691 ≤ (3322028733943/10000000000000 : ℝ)^3667
        have hw : |(52818543/125000000 : ℝ)|=(52818543/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936475603/5000000000 : ℝ)|^4691 ≤ (742923104907/2500000000000 : ℝ)^3667
        have hw : |(1936475603/5000000000 : ℝ)|=(1936475603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1150733487/2500000000 : ℝ)|^4691 ≤ (1853139422387/5000000000000 : ℝ)^3667
        have hw : |(1150733487/2500000000 : ℝ)|=(1150733487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_4 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1705229/9765625 : ℝ)*x 0 + (258648357/500000000 : ℝ)*x 1 + (342001763/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1705229/9765625 : ℝ)^4691 ≤ (10725962304161/100000000000000 : ℝ)^3667 := by
    have hnat : (1705229 : ℕ)^4691*100000000000000^3667 ≤ 10725962304161^3667*9765625^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705229 9765625 10725962304161 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258648357/500000000 : ℝ)^4691 ≤ (21516533391997/50000000000000 : ℝ)^3667 := by
    have hnat : (258648357 : ℕ)^4691*50000000000000^3667 ≤ 21516533391997^3667*500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258648357 500000000 21516533391997 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342001763/625000000 : ℝ)^4691 ≤ (9248194179341/20000000000000 : ℝ)^3667 := by
    have hnat : (342001763 : ℕ)^4691*20000000000000^3667 ≤ 9248194179341^3667*625000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342001763 625000000 9248194179341 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1705229/9765625 : ℝ), (258648357/500000000 : ℝ), (342001763/625000000 : ℝ)] ![(10725962304161/100000000000000 : ℝ), (21516533391997/50000000000000 : ℝ), (9248194179341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1705229/9765625 : ℝ)|^4691 ≤ (10725962304161/100000000000000 : ℝ)^3667
        have hw : |(-1705229/9765625 : ℝ)|=(1705229/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258648357/500000000 : ℝ)|^4691 ≤ (21516533391997/50000000000000 : ℝ)^3667
        have hw : |(258648357/500000000 : ℝ)|=(258648357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342001763/625000000 : ℝ)|^4691 ≤ (9248194179341/20000000000000 : ℝ)^3667
        have hw : |(342001763/625000000 : ℝ)|=(342001763/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_5 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105561047/200000000 : ℝ)*x 0 + (-800867779/5000000000 : ℝ)*x 1 + (5472028331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105561047/200000000 : ℝ)^4691 ≤ (11038631074283/25000000000000 : ℝ)^3667 := by
    have hnat : (105561047 : ℕ)^4691*25000000000000^3667 ≤ 11038631074283^3667*200000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105561047 200000000 11038631074283 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800867779/5000000000 : ℝ)^4691 ≤ (9604503460697/100000000000000 : ℝ)^3667 := by
    have hnat : (800867779 : ℕ)^4691*100000000000000^3667 ≤ 9604503460697^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800867779 5000000000 9604503460697 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472028331/10000000000 : ℝ)^4691 ≤ (23120486113179/50000000000000 : ℝ)^3667 := by
    have hnat : (5472028331 : ℕ)^4691*50000000000000^3667 ≤ 23120486113179^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472028331 10000000000 23120486113179 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105561047/200000000 : ℝ), (-800867779/5000000000 : ℝ), (5472028331/10000000000 : ℝ)] ![(11038631074283/25000000000000 : ℝ), (9604503460697/100000000000000 : ℝ), (23120486113179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105561047/200000000 : ℝ)|^4691 ≤ (11038631074283/25000000000000 : ℝ)^3667
        have hw : |(105561047/200000000 : ℝ)|=(105561047/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-800867779/5000000000 : ℝ)|^4691 ≤ (9604503460697/100000000000000 : ℝ)^3667
        have hw : |(-800867779/5000000000 : ℝ)|=(800867779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472028331/10000000000 : ℝ)|^4691 ≤ (23120486113179/50000000000000 : ℝ)^3667
        have hw : |(5472028331/10000000000 : ℝ)|=(5472028331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_6 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319513127/2500000000 : ℝ)*x 0 + (342001751/625000000 : ℝ)*x 1 + (-800867891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319513127/2500000000 : ℝ)^4691 ≤ (44154525988013/100000000000000 : ℝ)^3667 := by
    have hnat : (1319513127 : ℕ)^4691*100000000000000^3667 ≤ 44154525988013^3667*2500000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319513127 2500000000 44154525988013 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342001751/625000000 : ℝ)^4691 ≤ (46240968821149/100000000000000 : ℝ)^3667 := by
    have hnat : (342001751 : ℕ)^4691*100000000000000^3667 ≤ 46240968821149^3667*625000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342001751 625000000 46240968821149 100000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800867891/5000000000 : ℝ)^4691 ≤ (2401126294737/25000000000000 : ℝ)^3667 := by
    have hnat : (800867891 : ℕ)^4691*25000000000000^3667 ≤ 2401126294737^3667*5000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800867891 5000000000 2401126294737 25000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319513127/2500000000 : ℝ), (342001751/625000000 : ℝ), (-800867891/5000000000 : ℝ)] ![(44154525988013/100000000000000 : ℝ), (46240968821149/100000000000000 : ℝ), (2401126294737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319513127/2500000000 : ℝ)|^4691 ≤ (44154525988013/100000000000000 : ℝ)^3667
        have hw : |(1319513127/2500000000 : ℝ)|=(1319513127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342001751/625000000 : ℝ)|^4691 ≤ (46240968821149/100000000000000 : ℝ)^3667
        have hw : |(342001751/625000000 : ℝ)|=(342001751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-800867891/5000000000 : ℝ)|^4691 ≤ (2401126294737/25000000000000 : ℝ)^3667
        have hw : |(-800867891/5000000000 : ℝ)|=(800867891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1593_s2_7 (p : ℝ) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225694691/10000000000 : ℝ)*x 0 + (4597210873/10000000000 : ℝ)*x 1 + (3878738303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225694691/10000000000 : ℝ)^4691 ≤ (1328896478777/4000000000000 : ℝ)^3667 := by
    have hnat : (4225694691 : ℕ)^4691*4000000000000^3667 ≤ 1328896478777^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225694691 10000000000 1328896478777 4000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4597210873/10000000000 : ℝ)^4691 ≤ (7400769641957/20000000000000 : ℝ)^3667 := by
    have hnat : (4597210873 : ℕ)^4691*20000000000000^3667 ≤ 7400769641957^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597210873 10000000000 7400769641957 20000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3878738303/10000000000 : ℝ)^4691 ≤ (14886869903601/50000000000000 : ℝ)^3667 := by
    have hnat : (3878738303 : ℕ)^4691*50000000000000^3667 ≤ 14886869903601^3667*10000000000^4691 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3878738303 10000000000 14886869903601 50000000000000 4691 3667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4691/1024 : ℝ)) 4691 3667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225694691/10000000000 : ℝ), (4597210873/10000000000 : ℝ), (3878738303/10000000000 : ℝ)] ![(1328896478777/4000000000000 : ℝ), (7400769641957/20000000000000 : ℝ), (14886869903601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225694691/10000000000 : ℝ)|^4691 ≤ (1328896478777/4000000000000 : ℝ)^3667
        have hw : |(4225694691/10000000000 : ℝ)|=(4225694691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4597210873/10000000000 : ℝ)|^4691 ≤ (7400769641957/20000000000000 : ℝ)^3667
        have hw : |(4597210873/10000000000 : ℝ)|=(4597210873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3878738303/10000000000 : ℝ)|^4691 ≤ (14886869903601/50000000000000 : ℝ)^3667
        have hw : |(3878738303/10000000000 : ℝ)|=(3878738303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1593_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1267/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16571/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1101/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1101/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1101/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1101/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1101/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1101/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1101/12500 : ℝ) ^ (4687/1024 : ℝ) ≤ (29619437409141/2000000000000000000 : ℝ) := by
    have hpowers : (1101/12500 : ℝ)^4687 ≤ (29619437409141/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1101 : ℕ)^4687*2000000000000000000^1024 ≤ 29619437409141^1024*12500^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1101 12500 29619437409141 2000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1101/12500 : ℝ)) (X := (29619437409141/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18071/100000 : ℝ) ^ (4687/1024 : ℝ) ≤ (39728043081549881/100000000000000000000 : ℝ) := by
    have hpowers : (18071/100000 : ℝ)^4687 ≤ (39728043081549881/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18071 : ℕ)^4687*100000000000000000000^1024 ≤ 39728043081549881^1024*100000^4687 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18071 100000 39728043081549881 100000000000000000000 4687 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18071/100000 : ℝ)) (X := (39728043081549881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000029619437409141/1000000000000000000 : ℝ) ≤ (10000064710801933/10000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (1000029619437409141/1000000000000000000 : ℝ)^1024 ≤ (10000064710801933/10000000000000000 : ℝ)^4687 := by
      have hnat : (1000029619437409141 : ℕ)^1024*10000000000000000^4687 ≤ 10000064710801933^4687*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000029619437409141 1000000000000000000 10000064710801933 10000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064710801933/10000000000000000 : ℝ)) (X := (1000029619437409141/1000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041209014952006931/100000000000000000000 : ℝ) ≤ (1250112521969983/1250000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (100041209014952006931/100000000000000000000 : ℝ)^1024 ≤ (1250112521969983/1250000000000000 : ℝ)^4687 := by
      have hnat : (100041209014952006931 : ℕ)^1024*1250000000000000^4687 ≤ 1250112521969983^4687*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041209014952006931 100000000000000000000 1250112521969983 1250000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250112521969983/1250000000000000 : ℝ)) (X := (100041209014952006931/100000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039728043081549881/50000000000000000000 : ℝ) ≤ (2000347128143559/2000000000000000 : ℝ) ^ (4687/1024 : ℝ) := by
    have hpowers : (50039728043081549881/50000000000000000000 : ℝ)^1024 ≤ (2000347128143559/2000000000000000 : ℝ)^4687 := by
      have hnat : (50039728043081549881 : ℕ)^1024*2000000000000000^4687 ≤ 2000347128143559^4687*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039728043081549881 50000000000000000000 2000347128143559 2000000000000000 1024 4687 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000347128143559/2000000000000000 : ℝ)) (X := (50039728043081549881/50000000000000000000 : ℝ)) (by norm_num) 4687 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29619437409141/2000000000000000000 : ℝ) ≤ ((92615881865459392883/92630000000000000000 : ℝ)+2*(835464957931/926300000000000 : ℝ)*(1101/12500 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (92615881865459392883/92630000000000000000 : ℝ)+2*(835464957931/926300000000000 : ℝ)*(1101/12500 : ℝ)=(10000064710801933/10000000000000000 : ℝ) by norm_num, show 1+2*(29619437409141/2000000000000000000 : ℝ)=(1000029619437409141/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39728043081549881/100000000000000000000 : ℝ)+(29619437409141/2000000000000000000 : ℝ) ≤ ((92615881865459392883/92630000000000000000 : ℝ)+(835464957931/926300000000000 : ℝ)*((18071/100000 : ℝ)+(1101/12500 : ℝ)))^(4687/1024 : ℝ) := by
    rw [show (92615881865459392883/92630000000000000000 : ℝ)+(835464957931/926300000000000 : ℝ)*((18071/100000 : ℝ)+(1101/12500 : ℝ))=(1250112521969983/1250000000000000 : ℝ) by norm_num, show 1+(39728043081549881/100000000000000000000 : ℝ)+(29619437409141/2000000000000000000 : ℝ)=(100041209014952006931/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39728043081549881/100000000000000000000 : ℝ) ≤ ((92615881865459392883/92630000000000000000 : ℝ)+2*(835464957931/926300000000000 : ℝ)*(18071/100000 : ℝ))^(4687/1024 : ℝ) := by
    rw [show (92615881865459392883/92630000000000000000 : ℝ)+2*(835464957931/926300000000000 : ℝ)*(18071/100000 : ℝ)=(2000347128143559/2000000000000000 : ℝ) by norm_num, show 1+2*(39728043081549881/100000000000000000000 : ℝ)=(50039728043081549881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (92615881865459392883/92630000000000000000 : ℝ)*(X 1 0+X 2 0)+(835464957931/926300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (1101/12500 : ℝ)) (hi := (18071/100000 : ℝ)) (c := (92615881865459392883/92630000000000000000 : ℝ)) (alpha := (835464957931/926300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (92615881865459392883/92630000000000000000 : ℝ)*(X 0 1+X 2 1)+(835464957931/926300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (1101/12500 : ℝ)) (hi := (18071/100000 : ℝ)) (c := (92615881865459392883/92630000000000000000 : ℝ)) (alpha := (835464957931/926300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (92615881865459392883/92630000000000000000 : ℝ)*(X 0 2+X 1 2)+(835464957931/926300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4687/1024 : ℝ)) (lo := (1101/12500 : ℝ)) (hi := (18071/100000 : ℝ)) (c := (92615881865459392883/92630000000000000000 : ℝ)) (alpha := (835464957931/926300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-873033421/5000000000 : ℝ)*X 0 0+(684304639/1250000000 : ℝ)*X 0 1+(5170584551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358498347/10000000000 : ℝ)*X 1 0+(-951589631/5000000000 : ℝ)*X 1 1+(2585292259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358498067/10000000000 : ℝ)*X 2 0+(2585292463/5000000000 : ℝ)*X 2 1+(-1903179097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((52818543/125000000 : ℝ)*X 0 0+(1936475603/5000000000 : ℝ)*X 0 1+(1150733487/2500000000 : ℝ)*X 0 2+(52818543/125000000 : ℝ)*X 1 0+(1936475603/5000000000 : ℝ)*X 1 1+(1150733487/2500000000 : ℝ)*X 1 2+(52818543/125000000 : ℝ)*X 2 0+(1936475603/5000000000 : ℝ)*X 2 1+(1150733487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1705229/9765625 : ℝ)*X 0 0+(258648357/500000000 : ℝ)*X 0 1+(342001763/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105561047/200000000 : ℝ)*X 1 0+(-800867779/5000000000 : ℝ)*X 1 1+(5472028331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319513127/2500000000 : ℝ)*X 2 0+(342001751/625000000 : ℝ)*X 2 1+(-800867891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4225694691/10000000000 : ℝ)*X 0 0+(4597210873/10000000000 : ℝ)*X 0 1+(3878738303/10000000000 : ℝ)*X 0 2+(4225694691/10000000000 : ℝ)*X 1 0+(4597210873/10000000000 : ℝ)*X 1 1+(3878738303/10000000000 : ℝ)*X 1 2+(4225694691/10000000000 : ℝ)*X 2 0+(4597210873/10000000000 : ℝ)*X 2 1+(3878738303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1593_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14338595622424427710401/1447343750000000000000000000 : ℝ) := by norm_num
    linear_combination (836654097/50000000000000 : ℝ)*(base19) + (1421231563/100000000000000 : ℝ)*(base23) + (10731063/25000000000000 : ℝ)*(lower2) + (217737669/100000000000000 : ℝ)*(upper3) + (245381317/100000000000000 : ℝ)*(upper5) + (2330509094933061/100000000000000 : ℝ)*(major0) + (2330509094933061/100000000000000 : ℝ)*(major1) + (2330509094933061/100000000000000 : ℝ)*(major2) + (822772066634877/25000000000000 : ℝ)*(sp0) + (1645552908888349/50000000000000 : ℝ)*(sp1) + (329110606985333/10000000000000 : ℝ)*(sp2) + (684951485860963/50000000000000 : ℝ)*(sp3) + (3844909077/20000000000000 : ℝ)*(sp4) + (7396831467/100000000000000 : ℝ)*(sp7) + (1369910368553393/100000000000000 : ℝ)*(f.failure) + (822776872771223/25000000000000 : ℝ)*(f.sum) + (182709687969/11578750000000000000000000000 : ℝ)*base65 + (23039635200354904863/9263000000000000000000000000000000 : ℝ)*base67 + (5928841986367095137/9263000000000000000000000000000000 : ℝ)*base70 + (26662029681945095137/9263000000000000000000000000000000 : ℝ)*base72 + (136696073560463/23157500000000000000000000000 : ℝ)*base73 + (78662721278144904863/9263000000000000000000000000000000 : ℝ)*base75 + (7329522322302904863/9263000000000000000000000000000000 : ℝ)*base77 + (1746613140837095137/9263000000000000000000000000000000 : ℝ)*base80 + (74482605579497/23157500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (28836781/10000000000000000000000 : ℝ)*base90 + (28836781/10000000000000000000000 : ℝ)*base92 + (28836781/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1918231243928076675214458369/463150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193434149/100000000000000 : ℝ)*(base19) + (800663/160000000000 : ℝ)*(base23) + (68191349/100000000000000 : ℝ)*(upper3) + (102231427/100000000000000 : ℝ)*(lower4) + (800827/25000000000000 : ℝ)*(upper5) + (236781907207719/10000000000000 : ℝ)*(major0) + (236781907207719/10000000000000 : ℝ)*(major1) + (236781907207719/10000000000000 : ℝ)*(major2) + (200779637/10000000000000 : ℝ)*(sp1) + (11223763/390625000000 : ℝ)*(sp2) + (1671898119335103/50000000000000 : ℝ)*(sp4) + (417974254679961/12500000000000 : ℝ)*(sp5) + (3343792864972503/100000000000000 : ℝ)*(sp6) + (278368353485459/20000000000000 : ℝ)*(sp7) + (278368353485459/20000000000000 : ℝ)*(f.failure) + (1671898119335103/50000000000000 : ℝ)*(f.sum) + (57855280230169/9263000000000000000000000000 : ℝ)*base66 + (3689451960387663877/926300000000000000000000000000000 : ℝ)*base67 + (380669587322263877/926300000000000000000000000000000 : ℝ)*base69 + (2082461043370336123/926300000000000000000000000000000 : ℝ)*base72 + (1597081932191/1852600000000000000000000000 : ℝ)*base74 + (5007830135579736123/926300000000000000000000000000000 : ℝ)*base76 + (6391102273376663877/926300000000000000000000000000000 : ℝ)*base77 + (1434349659570863877/926300000000000000000000000000000 : ℝ)*base79 + (28518790055871/9263000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6923897/2000000000000000000000 : ℝ)*base89 + (6923897/2000000000000000000000 : ℝ)*base91 + (6923897/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1593_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1101/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1593_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1593_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1593_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1593_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1593_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4687/1024 : ℝ) ≤ p) (hpb : p ≤ (4691/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (170121283/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16571/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1593_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
