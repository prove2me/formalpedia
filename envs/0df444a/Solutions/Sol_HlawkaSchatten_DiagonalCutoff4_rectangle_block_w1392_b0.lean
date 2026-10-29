-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:46.243846+00:00
-- url     : https://prove2.me/submissions/2ba4c168-d841-4700-8e26-de5470fd91a7

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
theorem support_rectangle_w1392_s0_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1779954083/10000000000 : ℝ)*x 0 + (2987799901/5000000000 : ℝ)*x 1 + (4822697591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1779954083/10000000000 : ℝ)^17 ≤ (5232814709981/50000000000000 : ℝ)^13 := by
    have hnat : (1779954083 : ℕ)^17*50000000000000^13 ≤ 5232814709981^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779954083 10000000000 5232814709981 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2987799901/5000000000 : ℝ)^17 ≤ (51000661978027/100000000000000 : ℝ)^13 := by
    have hnat : (2987799901 : ℕ)^17*100000000000000^13 ≤ 51000661978027^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987799901 5000000000 51000661978027 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4822697591/10000000000 : ℝ)^17 ≤ (1204178393387/3125000000000 : ℝ)^13 := by
    have hnat : (4822697591 : ℕ)^17*3125000000000^13 ≤ 1204178393387^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822697591 10000000000 1204178393387 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1779954083/10000000000 : ℝ), (2987799901/5000000000 : ℝ), (4822697591/10000000000 : ℝ)] ![(5232814709981/50000000000000 : ℝ), (51000661978027/100000000000000 : ℝ), (1204178393387/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1779954083/10000000000 : ℝ)|^17 ≤ (5232814709981/50000000000000 : ℝ)^13
        have hw : |(-1779954083/10000000000 : ℝ)|=(1779954083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2987799901/5000000000 : ℝ)|^17 ≤ (51000661978027/100000000000000 : ℝ)^13
        have hw : |(2987799901/5000000000 : ℝ)|=(2987799901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4822697591/10000000000 : ℝ)|^17 ≤ (1204178393387/3125000000000 : ℝ)^13
        have hw : |(4822697591/10000000000 : ℝ)|=(4822697591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2748110973/5000000000 : ℝ)*x 0 + (-2432913923/10000000000 : ℝ)*x 1 + (4822697707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748110973/5000000000 : ℝ)^17 ≤ (2857354021719/6250000000000 : ℝ)^13 := by
    have hnat : (2748110973 : ℕ)^17*6250000000000^13 ≤ 2857354021719^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748110973 5000000000 2857354021719 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432913923/10000000000 : ℝ)^17 ≤ (15748625836283/100000000000000 : ℝ)^13 := by
    have hnat : (2432913923 : ℕ)^17*100000000000000^13 ≤ 15748625836283^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432913923 10000000000 15748625836283 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4822697707/10000000000 : ℝ)^17 ≤ (1204178431263/3125000000000 : ℝ)^13 := by
    have hnat : (4822697707 : ℕ)^17*3125000000000^13 ≤ 1204178431263^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822697707 10000000000 1204178431263 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748110973/5000000000 : ℝ), (-2432913923/10000000000 : ℝ), (4822697707/10000000000 : ℝ)] ![(2857354021719/6250000000000 : ℝ), (15748625836283/100000000000000 : ℝ), (1204178431263/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748110973/5000000000 : ℝ)|^17 ≤ (2857354021719/6250000000000 : ℝ)^13
        have hw : |(2748110973/5000000000 : ℝ)|=(2748110973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2432913923/10000000000 : ℝ)|^17 ≤ (15748625836283/100000000000000 : ℝ)^13
        have hw : |(-2432913923/10000000000 : ℝ)|=(2432913923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4822697707/10000000000 : ℝ)|^17 ≤ (1204178431263/3125000000000 : ℝ)^13
        have hw : |(4822697707/10000000000 : ℝ)|=(4822697707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2748110979/5000000000 : ℝ)*x 0 + (4822697677/10000000000 : ℝ)*x 1 + (-486582789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748110979/5000000000 : ℝ)^17 ≤ (45717664478033/100000000000000 : ℝ)^13 := by
    have hnat : (2748110979 : ℕ)^17*100000000000000^13 ≤ 45717664478033^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748110979 5000000000 45717664478033 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4822697677/10000000000 : ℝ)^17 ≤ (481671368587/1250000000000 : ℝ)^13 := by
    have hnat : (4822697677 : ℕ)^17*1250000000000^13 ≤ 481671368587^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822697677 10000000000 481671368587 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486582789/2000000000 : ℝ)^17 ≤ (1574862602251/10000000000000 : ℝ)^13 := by
    have hnat : (486582789 : ℕ)^17*10000000000000^13 ≤ 1574862602251^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486582789 2000000000 1574862602251 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748110979/5000000000 : ℝ), (4822697677/10000000000 : ℝ), (-486582789/2000000000 : ℝ)] ![(45717664478033/100000000000000 : ℝ), (481671368587/1250000000000 : ℝ), (1574862602251/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748110979/5000000000 : ℝ)|^17 ≤ (45717664478033/100000000000000 : ℝ)^13
        have hw : |(2748110979/5000000000 : ℝ)|=(2748110979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4822697677/10000000000 : ℝ)|^17 ≤ (481671368587/1250000000000 : ℝ)^13
        have hw : |(4822697677/10000000000 : ℝ)|=(4822697677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-486582789/2000000000 : ℝ)|^17 ≤ (1574862602251/10000000000000 : ℝ)^13
        have hw : |(-486582789/2000000000 : ℝ)|=(486582789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4171355167/10000000000 : ℝ)*x 0 + (776114321/2500000000 : ℝ)*x 1 + (222591983/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4171355167/10000000000 : ℝ)^17 ≤ (3984275748809/12500000000000 : ℝ)^13 := by
    have hnat : (4171355167 : ℕ)^17*12500000000000^13 ≤ 3984275748809^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171355167 10000000000 3984275748809 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776114321/2500000000 : ℝ)^17 ≤ (42306162353/195312500000 : ℝ)^13 := by
    have hnat : (776114321 : ℕ)^17*195312500000^13 ≤ 42306162353^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776114321 2500000000 42306162353 195312500000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222591983/400000000 : ℝ)^17 ≤ (46465038864447/100000000000000 : ℝ)^13 := by
    have hnat : (222591983 : ℕ)^17*100000000000000^13 ≤ 46465038864447^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222591983 400000000 46465038864447 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4171355167/10000000000 : ℝ), (776114321/2500000000 : ℝ), (222591983/400000000 : ℝ)] ![(3984275748809/12500000000000 : ℝ), (42306162353/195312500000 : ℝ), (46465038864447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4171355167/10000000000 : ℝ)|^17 ≤ (3984275748809/12500000000000 : ℝ)^13
        have hw : |(4171355167/10000000000 : ℝ)|=(4171355167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776114321/2500000000 : ℝ)|^17 ≤ (42306162353/195312500000 : ℝ)^13
        have hw : |(776114321/2500000000 : ℝ)|=(776114321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(222591983/400000000 : ℝ)|^17 ≤ (46465038864447/100000000000000 : ℝ)^13
        have hw : |(222591983/400000000 : ℝ)|=(222591983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784154453/10000000000 : ℝ)*x 0 + (2426137481/5000000000 : ℝ)*x 1 + (5944965239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784154453/10000000000 : ℝ)^17 ≤ (2099587441623/20000000000000 : ℝ)^13 := by
    have hnat : (1784154453 : ℕ)^17*20000000000000^13 ≤ 2099587441623^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784154453 10000000000 2099587441623 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2426137481/5000000000 : ℝ)^17 ≤ (7768608127101/20000000000000 : ℝ)^13 := by
    have hnat : (2426137481 : ℕ)^17*20000000000000^13 ≤ 7768608127101^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2426137481 5000000000 7768608127101 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5944965239/10000000000 : ℝ)^17 ≤ (50659022150453/100000000000000 : ℝ)^13 := by
    have hnat : (5944965239 : ℕ)^17*100000000000000^13 ≤ 50659022150453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944965239 10000000000 50659022150453 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784154453/10000000000 : ℝ), (2426137481/5000000000 : ℝ), (5944965239/10000000000 : ℝ)] ![(2099587441623/20000000000000 : ℝ), (7768608127101/20000000000000 : ℝ), (50659022150453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784154453/10000000000 : ℝ)|^17 ≤ (2099587441623/20000000000000 : ℝ)^13
        have hw : |(-1784154453/10000000000 : ℝ)|=(1784154453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2426137481/5000000000 : ℝ)|^17 ≤ (7768608127101/20000000000000 : ℝ)^13
        have hw : |(2426137481/5000000000 : ℝ)|=(2426137481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5944965239/10000000000 : ℝ)|^17 ≤ (50659022150453/100000000000000 : ℝ)^13
        have hw : |(5944965239/10000000000 : ℝ)|=(5944965239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2590867161/5000000000 : ℝ)*x 0 + (-52425857/400000000 : ℝ)*x 1 + (5944963077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590867161/5000000000 : ℝ)^17 ≤ (42327375368551/100000000000000 : ℝ)^13 := by
    have hnat : (2590867161 : ℕ)^17*100000000000000^13 ≤ 42327375368551^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590867161 5000000000 42327375368551 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52425857/400000000 : ℝ)^17 ≤ (7013626568161/100000000000000 : ℝ)^13 := by
    have hnat : (52425857 : ℕ)^17*100000000000000^13 ≤ 7013626568161^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52425857 400000000 7013626568161 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5944963077/10000000000 : ℝ)^17 ≤ (50658998058683/100000000000000 : ℝ)^13 := by
    have hnat : (5944963077 : ℕ)^17*100000000000000^13 ≤ 50658998058683^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944963077 10000000000 50658998058683 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590867161/5000000000 : ℝ), (-52425857/400000000 : ℝ), (5944963077/10000000000 : ℝ)] ![(42327375368551/100000000000000 : ℝ), (7013626568161/100000000000000 : ℝ), (50658998058683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590867161/5000000000 : ℝ)|^17 ≤ (42327375368551/100000000000000 : ℝ)^13
        have hw : |(2590867161/5000000000 : ℝ)|=(2590867161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-52425857/400000000 : ℝ)|^17 ≤ (7013626568161/100000000000000 : ℝ)^13
        have hw : |(-52425857/400000000 : ℝ)|=(52425857/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5944963077/10000000000 : ℝ)|^17 ≤ (50658998058683/100000000000000 : ℝ)^13
        have hw : |(5944963077/10000000000 : ℝ)|=(5944963077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1295432453/2500000000 : ℝ)*x 0 + (2972484167/5000000000 : ℝ)*x 1 + (-1310644937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295432453/2500000000 : ℝ)^17 ≤ (42327327192827/100000000000000 : ℝ)^13 := by
    have hnat : (1295432453 : ℕ)^17*100000000000000^13 ≤ 42327327192827^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295432453 2500000000 42327327192827 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2972484167/5000000000 : ℝ)^17 ≤ (12664764159727/25000000000000 : ℝ)^13 := by
    have hnat : (2972484167 : ℕ)^17*25000000000000^13 ≤ 12664764159727^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972484167 5000000000 12664764159727 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310644937/10000000000 : ℝ)^17 ≤ (7013616155409/100000000000000 : ℝ)^13 := by
    have hnat : (1310644937 : ℕ)^17*100000000000000^13 ≤ 7013616155409^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310644937 10000000000 7013616155409 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295432453/2500000000 : ℝ), (2972484167/5000000000 : ℝ), (-1310644937/10000000000 : ℝ)] ![(42327327192827/100000000000000 : ℝ), (12664764159727/25000000000000 : ℝ), (7013616155409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295432453/2500000000 : ℝ)|^17 ≤ (42327327192827/100000000000000 : ℝ)^13
        have hw : |(1295432453/2500000000 : ℝ)|=(1295432453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2972484167/5000000000 : ℝ)|^17 ≤ (12664764159727/25000000000000 : ℝ)^13
        have hw : |(2972484167/5000000000 : ℝ)|=(2972484167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1310644937/10000000000 : ℝ)|^17 ≤ (7013616155409/100000000000000 : ℝ)^13
        have hw : |(-1310644937/10000000000 : ℝ)|=(1310644937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s0_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4180311311/10000000000 : ℝ)*x 0 + (110033637/200000000 : ℝ)*x 1 + (1584918179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180311311/10000000000 : ℝ)^17 ≤ (31963728490663/100000000000000 : ℝ)^13 := by
    have hnat : (4180311311 : ℕ)^17*100000000000000^13 ≤ 31963728490663^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180311311 10000000000 31963728490663 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110033637/200000000 : ℝ)^17 ≤ (45777063014857/100000000000000 : ℝ)^13 := by
    have hnat : (110033637 : ℕ)^17*100000000000000^13 ≤ 45777063014857^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110033637 200000000 45777063014857 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584918179/5000000000 : ℝ)^17 ≤ (22259208477583/100000000000000 : ℝ)^13 := by
    have hnat : (1584918179 : ℕ)^17*100000000000000^13 ≤ 22259208477583^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584918179 5000000000 22259208477583 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180311311/10000000000 : ℝ), (110033637/200000000 : ℝ), (1584918179/5000000000 : ℝ)] ![(31963728490663/100000000000000 : ℝ), (45777063014857/100000000000000 : ℝ), (22259208477583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180311311/10000000000 : ℝ)|^17 ≤ (31963728490663/100000000000000 : ℝ)^13
        have hw : |(4180311311/10000000000 : ℝ)|=(4180311311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110033637/200000000 : ℝ)|^17 ≤ (45777063014857/100000000000000 : ℝ)^13
        have hw : |(110033637/200000000 : ℝ)|=(110033637/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584918179/5000000000 : ℝ)|^17 ≤ (22259208477583/100000000000000 : ℝ)^13
        have hw : |(1584918179/5000000000 : ℝ)|=(1584918179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1783/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6629/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4351/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4351 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4351*1^1024 ≤ 0^1024*1^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4351/1024 : ℝ) ≤ (2037715628945933807/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4351 ≤ (2037715628945933807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4351*100000000000000000000^1024 ≤ 2037715628945933807^1024*5^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2037715628945933807 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2037715628945933807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4351 := by
      have hnat : (1 : ℕ)^1024*1^4351 ≤ 1^4351*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102037715628945933807/100000000000000000000 : ℝ) ≤ (502379403223067/500000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (102037715628945933807/100000000000000000000 : ℝ)^1024 ≤ (502379403223067/500000000000000 : ℝ)^4351 := by
      have hnat : (102037715628945933807 : ℕ)^1024*500000000000000^4351 ≤ 502379403223067^4351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102037715628945933807 100000000000000000000 502379403223067 500000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502379403223067/500000000000000 : ℝ)) (X := (102037715628945933807/100000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52037715628945933807/50000000000000000000 : ℝ) ≤ (252379403223067/250000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (52037715628945933807/50000000000000000000 : ℝ)^1024 ≤ (252379403223067/250000000000000 : ℝ)^4351 := by
      have hnat : (52037715628945933807 : ℕ)^1024*250000000000000^4351 ≤ 252379403223067^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52037715628945933807 50000000000000000000 252379403223067 250000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252379403223067/250000000000000 : ℝ)) (X := (52037715628945933807/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2379403223067/200000000000000 : ℝ)*(0 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2379403223067/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2037715628945933807/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2379403223067/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2379403223067/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502379403223067/500000000000000 : ℝ) by norm_num, show 1+(2037715628945933807/100000000000000000000 : ℝ)+(0 : ℝ)=(102037715628945933807/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2037715628945933807/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2379403223067/200000000000000 : ℝ)*(2/5 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2379403223067/200000000000000 : ℝ)*(2/5 : ℝ)=(252379403223067/250000000000000 : ℝ) by norm_num, show 1+2*(2037715628945933807/100000000000000000000 : ℝ)=(52037715628945933807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2379403223067/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2379403223067/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2379403223067/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2379403223067/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2379403223067/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2379403223067/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1779954083/10000000000 : ℝ)*X 0 0+(2987799901/5000000000 : ℝ)*X 0 1+(4822697591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2748110973/5000000000 : ℝ)*X 1 0+(-2432913923/10000000000 : ℝ)*X 1 1+(4822697707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2748110979/5000000000 : ℝ)*X 2 0+(4822697677/10000000000 : ℝ)*X 2 1+(-486582789/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4171355167/10000000000 : ℝ)*X 0 0+(776114321/2500000000 : ℝ)*X 0 1+(222591983/400000000 : ℝ)*X 0 2+(4171355167/10000000000 : ℝ)*X 1 0+(776114321/2500000000 : ℝ)*X 1 1+(222591983/400000000 : ℝ)*X 1 2+(4171355167/10000000000 : ℝ)*X 2 0+(776114321/2500000000 : ℝ)*X 2 1+(222591983/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1784154453/10000000000 : ℝ)*X 0 0+(2426137481/5000000000 : ℝ)*X 0 1+(5944965239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2590867161/5000000000 : ℝ)*X 1 0+(-52425857/400000000 : ℝ)*X 1 1+(5944963077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1295432453/2500000000 : ℝ)*X 2 0+(2972484167/5000000000 : ℝ)*X 2 1+(-1310644937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180311311/10000000000 : ℝ)*X 0 0+(110033637/200000000 : ℝ)*X 0 1+(1584918179/5000000000 : ℝ)*X 0 2+(4180311311/10000000000 : ℝ)*X 1 0+(110033637/200000000 : ℝ)*X 1 1+(1584918179/5000000000 : ℝ)*X 1 2+(4180311311/10000000000 : ℝ)*X 2 0+(110033637/200000000 : ℝ)*X 2 1+(1584918179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23975096425878893787/5000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6487379/20000000000000 : ℝ)*(base1) + (70213617/6250000000000 : ℝ)*(base19) + (281327911/25000000000000 : ℝ)*(base23) + (71160969/50000000000000 : ℝ)*(upper3) + (4287707/3125000000000 : ℝ)*(upper5) + (79614689203/12500000000 : ℝ)*(major0) + (79614689203/12500000000 : ℝ)*(major1) + (79614689203/12500000000 : ℝ)*(major2) + (433689973149897/50000000000000 : ℝ)*(sp0) + (173476531030779/20000000000000 : ℝ)*(sp1) + (867382653260123/100000000000000 : ℝ)*(sp2) + (203224614217853/50000000000000 : ℝ)*(sp3) + (966177217/25000000000000 : ℝ)*(sp4) + (1827969651/100000000000000 : ℝ)*(sp7) + (406451088842251/100000000000000 : ℝ)*(f.failure) + (867383778571767/100000000000000 : ℝ)*(f.sum) + (8894553881/5000000000000000000000000 : ℝ)*base66 + (2297214011/625000000000000000000000 : ℝ)*base68 + (4032783421/625000000000000000000000 : ℝ)*base70 + (16113083963/5000000000000000000000000 : ℝ)*base72 + (16366901441/5000000000000000000000000 : ℝ)*base74 + (12992182663/5000000000000000000000000 : ℝ)*base76 + (19173089783/5000000000000000000000000 : ℝ)*base78 + (347864423/5000000000000000000000000 : ℝ)*base80 + (31082621461/5000000000000000000000000 : ℝ)*base82 + (3430537/1000000000000000000000 : ℝ)*base90 + (3430537/1000000000000000000000 : ℝ)*base92 + (3430537/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89247617303744188324053/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1693002743/100000000000000 : ℝ)*(base19) + (1715715197/100000000000000 : ℝ)*(base23) + (15662371/4000000000000 : ℝ)*(base39) + (41808113/20000000000000 : ℝ)*(upper2) + (34686679/10000000000000 : ℝ)*(upper5) + (42000429750179/6250000000000 : ℝ)*(major0) + (42000429750179/6250000000000 : ℝ)*(major1) + (672006484443589/100000000000000 : ℝ)*(major2) + (2177110751/50000000000000 : ℝ)*(sp1) + (4902092489/100000000000000 : ℝ)*(sp2) + (91516957754493/10000000000000 : ℝ)*(sp4) + (183032706064137/20000000000000 : ℝ)*(sp5) + (457581675648259/50000000000000 : ℝ)*(sp6) + (428843485409461/100000000000000 : ℝ)*(sp7) + (428843485409461/100000000000000 : ℝ)*(f.failure) + (183033993820841/20000000000000 : ℝ)*(f.sum) + (47529466311351/20000000000000000000000000000 : ℝ)*base65 + (53957765132537/20000000000000000000000000000 : ℝ)*base68 + (7230868956007/1250000000000000000000000000 : ℝ)*base70 + (29602191592537/20000000000000000000000000000 : ℝ)*base72 + (9345919648649/20000000000000000000000000000 : ℝ)*base74 + (9667313192257/1250000000000000000000000000 : ℝ)*base76 + (2968993367743/1250000000000000000000000000 : ℝ)*base77 + (2656355285243/1250000000000000000000000000 : ℝ)*base79 + (650856962691/312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6085193/1000000000000000000000 : ℝ)*base89 + (6085193/1000000000000000000000 : ℝ)*base91 + (6085193/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1783/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6629/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1392_s1_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1957578579/10000000000 : ℝ)*x 0 + (5620420257/10000000000 : ℝ)*x 1 + (633008073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1957578579/10000000000 : ℝ)^17 ≤ (5925931892873/50000000000000 : ℝ)^13 := by
    have hnat : (1957578579 : ℕ)^17*50000000000000^13 ≤ 5925931892873^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957578579 10000000000 5925931892873 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5620420257/10000000000 : ℝ)^17 ≤ (5884161512767/12500000000000 : ℝ)^13 := by
    have hnat : (5620420257 : ℕ)^17*12500000000000^13 ≤ 5884161512767^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620420257 10000000000 5884161512767 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633008073/1250000000 : ℝ)^17 ≤ (41074844096339/100000000000000 : ℝ)^13 := by
    have hnat : (633008073 : ℕ)^17*100000000000000^13 ≤ 41074844096339^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633008073 1250000000 41074844096339 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1957578579/10000000000 : ℝ), (5620420257/10000000000 : ℝ), (633008073/1250000000 : ℝ)] ![(5925931892873/50000000000000 : ℝ), (5884161512767/12500000000000 : ℝ), (41074844096339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1957578579/10000000000 : ℝ)|^17 ≤ (5925931892873/50000000000000 : ℝ)^13
        have hw : |(-1957578579/10000000000 : ℝ)|=(1957578579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5620420257/10000000000 : ℝ)|^17 ≤ (5884161512767/12500000000000 : ℝ)^13
        have hw : |(5620420257/10000000000 : ℝ)|=(5620420257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633008073/1250000000 : ℝ)|^17 ≤ (41074844096339/100000000000000 : ℝ)^13
        have hw : |(633008073/1250000000 : ℝ)|=(633008073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5400557207/10000000000 : ℝ)*x 0 + (-2253236789/10000000000 : ℝ)*x 1 + (633008249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400557207/10000000000 : ℝ)^17 ≤ (22339938930627/50000000000000 : ℝ)^13 := by
    have hnat : (5400557207 : ℕ)^17*50000000000000^13 ≤ 22339938930627^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400557207 10000000000 22339938930627 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253236789/10000000000 : ℝ)^17 ≤ (7122631545329/50000000000000 : ℝ)^13 := by
    have hnat : (2253236789 : ℕ)^17*50000000000000^13 ≤ 7122631545329^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253236789 10000000000 7122631545329 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (633008249/1250000000 : ℝ)^17 ≤ (41074859030641/100000000000000 : ℝ)^13 := by
    have hnat : (633008249 : ℕ)^17*100000000000000^13 ≤ 41074859030641^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633008249 1250000000 41074859030641 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400557207/10000000000 : ℝ), (-2253236789/10000000000 : ℝ), (633008249/1250000000 : ℝ)] ![(22339938930627/50000000000000 : ℝ), (7122631545329/50000000000000 : ℝ), (41074859030641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400557207/10000000000 : ℝ)|^17 ≤ (22339938930627/50000000000000 : ℝ)^13
        have hw : |(5400557207/10000000000 : ℝ)|=(5400557207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2253236789/10000000000 : ℝ)|^17 ≤ (7122631545329/50000000000000 : ℝ)^13
        have hw : |(-2253236789/10000000000 : ℝ)|=(2253236789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(633008249/1250000000 : ℝ)|^17 ≤ (41074859030641/100000000000000 : ℝ)^13
        have hw : |(633008249/1250000000 : ℝ)|=(633008249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2700279043/5000000000 : ℝ)*x 0 + (5064064767/10000000000 : ℝ)*x 1 + (-2253237211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700279043/5000000000 : ℝ)^17 ≤ (44679887370977/100000000000000 : ℝ)^13 := by
    have hnat : (2700279043 : ℕ)^17*100000000000000^13 ≤ 44679887370977^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700279043 5000000000 44679887370977 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064064767/10000000000 : ℝ)^17 ≤ (20537423018687/50000000000000 : ℝ)^13 := by
    have hnat : (5064064767 : ℕ)^17*50000000000000^13 ≤ 20537423018687^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064064767 10000000000 20537423018687 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253237211/10000000000 : ℝ)^17 ≤ (14245266579503/100000000000000 : ℝ)^13 := by
    have hnat : (2253237211 : ℕ)^17*100000000000000^13 ≤ 14245266579503^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253237211 10000000000 14245266579503 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700279043/5000000000 : ℝ), (5064064767/10000000000 : ℝ), (-2253237211/10000000000 : ℝ)] ![(44679887370977/100000000000000 : ℝ), (20537423018687/50000000000000 : ℝ), (14245266579503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700279043/5000000000 : ℝ)|^17 ≤ (44679887370977/100000000000000 : ℝ)^13
        have hw : |(2700279043/5000000000 : ℝ)|=(2700279043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064064767/10000000000 : ℝ)|^17 ≤ (20537423018687/50000000000000 : ℝ)^13
        have hw : |(5064064767/10000000000 : ℝ)|=(5064064767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2253237211/10000000000 : ℝ)|^17 ≤ (14245266579503/100000000000000 : ℝ)^13
        have hw : |(-2253237211/10000000000 : ℝ)|=(2253237211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2141669439/5000000000 : ℝ)*x 0 + (1863502489/5000000000 : ℝ)*x 1 + (2457143883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141669439/5000000000 : ℝ)^17 ≤ (32997780010797/100000000000000 : ℝ)^13 := by
    have hnat : (2141669439 : ℕ)^17*100000000000000^13 ≤ 32997780010797^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141669439 5000000000 32997780010797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863502489/5000000000 : ℝ)^17 ≤ (13754371111871/50000000000000 : ℝ)^13 := by
    have hnat : (1863502489 : ℕ)^17*50000000000000^13 ≤ 13754371111871^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863502489 5000000000 13754371111871 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2457143883/5000000000 : ℝ)^17 ≤ (7898695550421/20000000000000 : ℝ)^13 := by
    have hnat : (2457143883 : ℕ)^17*20000000000000^13 ≤ 7898695550421^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457143883 5000000000 7898695550421 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2141669439/5000000000 : ℝ), (1863502489/5000000000 : ℝ), (2457143883/5000000000 : ℝ)] ![(32997780010797/100000000000000 : ℝ), (13754371111871/50000000000000 : ℝ), (7898695550421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2141669439/5000000000 : ℝ)|^17 ≤ (32997780010797/100000000000000 : ℝ)^13
        have hw : |(2141669439/5000000000 : ℝ)|=(2141669439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1863502489/5000000000 : ℝ)|^17 ≤ (13754371111871/50000000000000 : ℝ)^13
        have hw : |(1863502489/5000000000 : ℝ)|=(1863502489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2457143883/5000000000 : ℝ)|^17 ≤ (7898695550421/20000000000000 : ℝ)^13
        have hw : |(2457143883/5000000000 : ℝ)|=(2457143883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-244753833/1250000000 : ℝ)*x 0 + (5070780787/10000000000 : ℝ)*x 1 + (1403396657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244753833/1250000000 : ℝ)^17 ≤ (11855443171813/100000000000000 : ℝ)^13 := by
    have hnat : (244753833 : ℕ)^17*100000000000000^13 ≤ 11855443171813^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244753833 1250000000 11855443171813 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5070780787/10000000000 : ℝ)^17 ≤ (41146095700723/100000000000000 : ℝ)^13 := by
    have hnat : (5070780787 : ℕ)^17*100000000000000^13 ≤ 41146095700723^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5070780787 10000000000 41146095700723 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403396657/2500000000 : ℝ)^17 ≤ (46998461113929/100000000000000 : ℝ)^13 := by
    have hnat : (1403396657 : ℕ)^17*100000000000000^13 ≤ 46998461113929^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403396657 2500000000 46998461113929 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-244753833/1250000000 : ℝ), (5070780787/10000000000 : ℝ), (1403396657/2500000000 : ℝ)] ![(11855443171813/100000000000000 : ℝ), (41146095700723/100000000000000 : ℝ), (46998461113929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-244753833/1250000000 : ℝ)|^17 ≤ (11855443171813/100000000000000 : ℝ)^13
        have hw : |(-244753833/1250000000 : ℝ)|=(244753833/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5070780787/10000000000 : ℝ)|^17 ≤ (41146095700723/100000000000000 : ℝ)^13
        have hw : |(5070780787/10000000000 : ℝ)|=(5070780787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1403396657/2500000000 : ℝ)|^17 ≤ (46998461113929/100000000000000 : ℝ)^13
        have hw : |(1403396657/2500000000 : ℝ)|=(1403396657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1051121119/2000000000 : ℝ)*x 0 + (-1703716011/10000000000 : ℝ)*x 1 + (5613586643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051121119/2000000000 : ℝ)^17 ≤ (21559095925763/50000000000000 : ℝ)^13 := by
    have hnat : (1051121119 : ℕ)^17*50000000000000^13 ≤ 21559095925763^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051121119 2000000000 21559095925763 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1703716011/10000000000 : ℝ)^17 ≤ (9883346852279/100000000000000 : ℝ)^13 := by
    have hnat : (1703716011 : ℕ)^17*100000000000000^13 ≤ 9883346852279^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703716011 10000000000 9883346852279 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5613586643/10000000000 : ℝ)^17 ≤ (23499230639077/50000000000000 : ℝ)^13 := by
    have hnat : (5613586643 : ℕ)^17*50000000000000^13 ≤ 23499230639077^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5613586643 10000000000 23499230639077 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051121119/2000000000 : ℝ), (-1703716011/10000000000 : ℝ), (5613586643/10000000000 : ℝ)] ![(21559095925763/50000000000000 : ℝ), (9883346852279/100000000000000 : ℝ), (23499230639077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051121119/2000000000 : ℝ)|^17 ≤ (21559095925763/50000000000000 : ℝ)^13
        have hw : |(1051121119/2000000000 : ℝ)|=(1051121119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1703716011/10000000000 : ℝ)|^17 ≤ (9883346852279/100000000000000 : ℝ)^13
        have hw : |(-1703716011/10000000000 : ℝ)|=(1703716011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5613586643/10000000000 : ℝ)|^17 ≤ (23499230639077/50000000000000 : ℝ)^13
        have hw : |(5613586643/10000000000 : ℝ)|=(5613586643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5255606033/10000000000 : ℝ)*x 0 + (280679351/500000000 : ℝ)*x 1 + (-1703714847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255606033/10000000000 : ℝ)^17 ≤ (42107613819/97656250000 : ℝ)^13 := by
    have hnat : (5255606033 : ℕ)^17*97656250000^13 ≤ 42107613819^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255606033 10000000000 42107613819 97656250000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280679351/500000000 : ℝ)^17 ≤ (46998465405683/100000000000000 : ℝ)^13 := by
    have hnat : (280679351 : ℕ)^17*100000000000000^13 ≤ 46998465405683^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280679351 500000000 46998465405683 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703714847/10000000000 : ℝ)^17 ≤ (1235417252773/12500000000000 : ℝ)^13 := by
    have hnat : (1703714847 : ℕ)^17*12500000000000^13 ≤ 1235417252773^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703714847 10000000000 1235417252773 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255606033/10000000000 : ℝ), (280679351/500000000 : ℝ), (-1703714847/10000000000 : ℝ)] ![(42107613819/97656250000 : ℝ), (46998465405683/100000000000000 : ℝ), (1235417252773/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255606033/10000000000 : ℝ)|^17 ≤ (42107613819/97656250000 : ℝ)^13
        have hw : |(5255606033/10000000000 : ℝ)|=(5255606033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280679351/500000000 : ℝ)|^17 ≤ (46998465405683/100000000000000 : ℝ)^13
        have hw : |(280679351/500000000 : ℝ)|=(280679351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1703714847/10000000000 : ℝ)|^17 ≤ (1235417252773/12500000000000 : ℝ)^13
        have hw : |(-1703714847/10000000000 : ℝ)|=(1703714847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s1_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2142152593/5000000000 : ℝ)*x 0 + (4899955537/10000000000 : ℝ)*x 1 + (3741585739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142152593/5000000000 : ℝ)^17 ≤ (16503757533957/50000000000000 : ℝ)^13 := by
    have hnat : (2142152593 : ℕ)^17*50000000000000^13 ≤ 16503757533957^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142152593 5000000000 16503757533957 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899955537/10000000000 : ℝ)^17 ≤ (19671462436171/50000000000000 : ℝ)^13 := by
    have hnat : (4899955537 : ℕ)^17*50000000000000^13 ≤ 19671462436171^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899955537 10000000000 19671462436171 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3741585739/10000000000 : ℝ)^17 ≤ (13824780018913/50000000000000 : ℝ)^13 := by
    have hnat : (3741585739 : ℕ)^17*50000000000000^13 ≤ 13824780018913^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741585739 10000000000 13824780018913 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142152593/5000000000 : ℝ), (4899955537/10000000000 : ℝ), (3741585739/10000000000 : ℝ)] ![(16503757533957/50000000000000 : ℝ), (19671462436171/50000000000000 : ℝ), (13824780018913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142152593/5000000000 : ℝ)|^17 ≤ (16503757533957/50000000000000 : ℝ)^13
        have hw : |(2142152593/5000000000 : ℝ)|=(2142152593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4899955537/10000000000 : ℝ)|^17 ≤ (19671462436171/50000000000000 : ℝ)^13
        have hw : |(4899955537/10000000000 : ℝ)|=(4899955537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3741585739/10000000000 : ℝ)|^17 ≤ (13824780018913/50000000000000 : ℝ)^13
        have hw : |(3741585739/10000000000 : ℝ)|=(3741585739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6629/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6629/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6629/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1783/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6629/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6629/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1783/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6629/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6629/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1783/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1783/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (1853834981059/50000000000000000000 : ℝ) := by
    have hpowers : (1783/100000 : ℝ)^4351 ≤ (1853834981059/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1783 : ℕ)^4351*50000000000000000000^1024 ≤ 1853834981059^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1783 100000 1853834981059 50000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1783/100000 : ℝ)) (X := (1853834981059/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6629/25000 : ℝ) ^ (4351/1024 : ℝ) ≤ (355199237182505653/100000000000000000000 : ℝ) := by
    have hpowers : (6629/25000 : ℝ)^4351 ≤ (355199237182505653/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6629 : ℕ)^4351*100000000000000000000^1024 ≤ 355199237182505653^1024*25000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6629 25000 355199237182505653 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6629/25000 : ℝ)) (X := (355199237182505653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001853834981059/25000000000000000000 : ℝ) ≤ (10000000174518683/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (25000001853834981059/25000000000000000000 : ℝ)^1024 ≤ (10000000174518683/10000000000000000 : ℝ)^4351 := by
      have hnat : (25000001853834981059 : ℕ)^1024*10000000000000000^4351 ≤ 10000000174518683^4351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001853834981059 25000000000000000000 10000000174518683 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000174518683/10000000000000000 : ℝ)) (X := (25000001853834981059/25000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100355202944852467771/100000000000000000000 : ℝ) ≤ (100083483082217/100000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (100355202944852467771/100000000000000000000 : ℝ)^1024 ≤ (100083483082217/100000000000000 : ℝ)^4351 := by
      have hnat : (100355202944852467771 : ℕ)^1024*100000000000000^4351 ≤ 100083483082217^4351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100355202944852467771 100000000000000000000 100083483082217 100000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100083483082217/100000000000000 : ℝ)) (X := (100355202944852467771/100000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50355199237182505653/50000000000000000000 : ℝ) ≤ (10016696441924717/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50355199237182505653/50000000000000000000 : ℝ)^1024 ≤ (10016696441924717/10000000000000000 : ℝ)^4351 := by
      have hnat : (50355199237182505653 : ℕ)^1024*10000000000000000^4351 ≤ 10016696441924717^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50355199237182505653 50000000000000000000 10016696441924717 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016696441924717/10000000000000000 : ℝ)) (X := (50355199237182505653/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1853834981059/50000000000000000000 : ℝ) ≤ ((247300234871585628017/247330000000000000000 : ℝ)+2*(8348133703017/2473300000000000 : ℝ)*(1783/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (247300234871585628017/247330000000000000000 : ℝ)+2*(8348133703017/2473300000000000 : ℝ)*(1783/100000 : ℝ)=(10000000174518683/10000000000000000 : ℝ) by norm_num, show 1+2*(1853834981059/50000000000000000000 : ℝ)=(25000001853834981059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(355199237182505653/100000000000000000000 : ℝ)+(1853834981059/50000000000000000000 : ℝ) ≤ ((247300234871585628017/247330000000000000000 : ℝ)+(8348133703017/2473300000000000 : ℝ)*((6629/25000 : ℝ)+(1783/100000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (247300234871585628017/247330000000000000000 : ℝ)+(8348133703017/2473300000000000 : ℝ)*((6629/25000 : ℝ)+(1783/100000 : ℝ))=(100083483082217/100000000000000 : ℝ) by norm_num, show 1+(355199237182505653/100000000000000000000 : ℝ)+(1853834981059/50000000000000000000 : ℝ)=(100355202944852467771/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(355199237182505653/100000000000000000000 : ℝ) ≤ ((247300234871585628017/247330000000000000000 : ℝ)+2*(8348133703017/2473300000000000 : ℝ)*(6629/25000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (247300234871585628017/247330000000000000000 : ℝ)+2*(8348133703017/2473300000000000 : ℝ)*(6629/25000 : ℝ)=(10016696441924717/10000000000000000 : ℝ) by norm_num, show 1+2*(355199237182505653/100000000000000000000 : ℝ)=(50355199237182505653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (247300234871585628017/247330000000000000000 : ℝ)*(X 1 0+X 2 0)+(8348133703017/2473300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (1783/100000 : ℝ)) (hi := (6629/25000 : ℝ)) (c := (247300234871585628017/247330000000000000000 : ℝ)) (alpha := (8348133703017/2473300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (247300234871585628017/247330000000000000000 : ℝ)*(X 0 1+X 2 1)+(8348133703017/2473300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (1783/100000 : ℝ)) (hi := (6629/25000 : ℝ)) (c := (247300234871585628017/247330000000000000000 : ℝ)) (alpha := (8348133703017/2473300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (247300234871585628017/247330000000000000000 : ℝ)*(X 0 2+X 1 2)+(8348133703017/2473300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (1783/100000 : ℝ)) (hi := (6629/25000 : ℝ)) (c := (247300234871585628017/247330000000000000000 : ℝ)) (alpha := (8348133703017/2473300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1957578579/10000000000 : ℝ)*X 0 0+(5620420257/10000000000 : ℝ)*X 0 1+(633008073/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400557207/10000000000 : ℝ)*X 1 0+(-2253236789/10000000000 : ℝ)*X 1 1+(633008249/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2700279043/5000000000 : ℝ)*X 2 0+(5064064767/10000000000 : ℝ)*X 2 1+(-2253237211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2141669439/5000000000 : ℝ)*X 0 0+(1863502489/5000000000 : ℝ)*X 0 1+(2457143883/5000000000 : ℝ)*X 0 2+(2141669439/5000000000 : ℝ)*X 1 0+(1863502489/5000000000 : ℝ)*X 1 1+(2457143883/5000000000 : ℝ)*X 1 2+(2141669439/5000000000 : ℝ)*X 2 0+(1863502489/5000000000 : ℝ)*X 2 1+(2457143883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-244753833/1250000000 : ℝ)*X 0 0+(5070780787/10000000000 : ℝ)*X 0 1+(1403396657/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051121119/2000000000 : ℝ)*X 1 0+(-1703716011/10000000000 : ℝ)*X 1 1+(5613586643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255606033/10000000000 : ℝ)*X 2 0+(280679351/500000000 : ℝ)*X 2 1+(-1703714847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142152593/5000000000 : ℝ)*X 0 0+(4899955537/10000000000 : ℝ)*X 0 1+(3741585739/10000000000 : ℝ)*X 0 2+(2142152593/5000000000 : ℝ)*X 1 0+(4899955537/10000000000 : ℝ)*X 1 1+(3741585739/10000000000 : ℝ)*X 1 2+(2142152593/5000000000 : ℝ)*X 2 0+(4899955537/10000000000 : ℝ)*X 2 1+(3741585739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10465937694972241701142077573/2473300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83529091/12500000000000 : ℝ)*(base19) + (1923393/200000000000 : ℝ)*(base23) + (11562931/100000000000000 : ℝ)*(upper2) + (11593129/10000000000000 : ℝ)*(upper3) + (2214011/20000000000000 : ℝ)*(upper4) + (263969382791859/20000000000000 : ℝ)*(major0) + (263969382791859/20000000000000 : ℝ)*(major1) + (263969382791859/20000000000000 : ℝ)*(major2) + (224677546050441/12500000000000 : ℝ)*(sp0) + (1797428198136697/100000000000000 : ℝ)*(sp1) + (71897116186917/4000000000000 : ℝ)*(sp2) + (210565396569323/25000000000000 : ℝ)*(sp3) + (8497965897/100000000000000 : ℝ)*(sp4) + (404277449/12500000000000 : ℝ)*(sp7) + (168452964099377/20000000000000 : ℝ)*(f.failure) + (112339304148089/6250000000000 : ℝ)*(f.sum) + (169370668326541/24733000000000000000000000000 : ℝ)*base66 + (24522366579511213603/4946600000000000000000000000000000 : ℝ)*base67 + (16438842036385413603/4946600000000000000000000000000000 : ℝ)*base69 + (4430466284928013603/4946600000000000000000000000000000 : ℝ)*base71 + (16102497826913/6183250000000000000000000000 : ℝ)*base73 + (8127412578755813603/4946600000000000000000000000000000 : ℝ)*base75 + (7697714030799413603/4946600000000000000000000000000000 : ℝ)*base77 + (7006229227367213603/4946600000000000000000000000000000 : ℝ)*base79 + (9310876420799/12366500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (757301/200000000000000000000 : ℝ)*base89 + (757301/200000000000000000000 : ℝ)*base91 + (757301/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (674310639577652330707749/123665000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187514223/100000000000000 : ℝ)*(base1) + (1439006153/100000000000000 : ℝ)*(base19) + (842918047/50000000000000 : ℝ)*(base23) + (67348887/50000000000000 : ℝ)*(upper3) + (219681291/100000000000000 : ℝ)*(upper5) + (676390828663083/50000000000000 : ℝ)*(major0) + (676390828663083/50000000000000 : ℝ)*(major1) + (676390828663083/50000000000000 : ℝ)*(major2) + (7170076207/100000000000000 : ℝ)*(sp1) + (5276353789/50000000000000 : ℝ)*(sp2) + (921140540416967/50000000000000 : ℝ)*(sp4) + (1842272284237351/100000000000000 : ℝ)*(sp5) + (1842268654776039/100000000000000 : ℝ)*(sp6) + (863282052061057/100000000000000 : ℝ)*(sp7) + (10791027994691/1250000000000 : ℝ)*(f.failure) + (1842280893319711/100000000000000 : ℝ)*(f.sum) + (51041773780867/30916250000000000000000000000 : ℝ)*base66 + (21364447637256003589/12366500000000000000000000000000000 : ℝ)*base68 + (18600963905811996411/12366500000000000000000000000000000 : ℝ)*base69 + (6648820541715496411/12366500000000000000000000000000000 : ℝ)*base71 + (29519316545197/123665000000000000000000000000 : ℝ)*base73 + (30139375871940503589/12366500000000000000000000000000000 : ℝ)*base76 + (34881956780398996411/12366500000000000000000000000000000 : ℝ)*base77 + (12414713248848003589/12366500000000000000000000000000000 : ℝ)*base80 + (99302387984521/61832500000000000000000000000 : ℝ)*base81 + (89183/12500000000000000000 : ℝ)*base89 + (89183/12500000000000000000 : ℝ)*base91 + (89183/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6629/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1783/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1392_s2_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-249195699/1250000000 : ℝ)*x 0 + (5466825199/10000000000 : ℝ)*x 1 + (2597271483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249195699/1250000000 : ℝ)^17 ≤ (12137583500567/100000000000000 : ℝ)^13 := by
    have hnat : (249195699 : ℕ)^17*100000000000000^13 ≤ 12137583500567^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249195699 1250000000 12137583500567 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466825199/10000000000 : ℝ)^17 ≤ (11349541858489/25000000000000 : ℝ)^13 := by
    have hnat : (5466825199 : ℕ)^17*25000000000000^13 ≤ 11349541858489^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466825199 10000000000 11349541858489 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597271483/5000000000 : ℝ)^17 ≤ (8492849810351/20000000000000 : ℝ)^13 := by
    have hnat : (2597271483 : ℕ)^17*20000000000000^13 ≤ 8492849810351^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597271483 5000000000 8492849810351 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249195699/1250000000 : ℝ), (5466825199/10000000000 : ℝ), (2597271483/5000000000 : ℝ)] ![(12137583500567/100000000000000 : ℝ), (11349541858489/25000000000000 : ℝ), (8492849810351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249195699/1250000000 : ℝ)|^17 ≤ (12137583500567/100000000000000 : ℝ)^13
        have hw : |(-249195699/1250000000 : ℝ)|=(249195699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466825199/10000000000 : ℝ)|^17 ≤ (11349541858489/25000000000000 : ℝ)^13
        have hw : |(5466825199/10000000000 : ℝ)|=(5466825199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597271483/5000000000 : ℝ)|^17 ≤ (8492849810351/20000000000000 : ℝ)^13
        have hw : |(2597271483/5000000000 : ℝ)|=(2597271483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1072507729/2000000000 : ℝ)*x 0 + (-21338933/100000000 : ℝ)*x 1 + (2597271459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072507729/2000000000 : ℝ)^17 ≤ (44269008949189/100000000000000 : ℝ)^13 := by
    have hnat : (1072507729 : ℕ)^17*100000000000000^13 ≤ 44269008949189^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072507729 2000000000 44269008949189 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21338933/100000000 : ℝ)^17 ≤ (132667424987/1000000000000 : ℝ)^13 := by
    have hnat : (21338933 : ℕ)^17*1000000000000^13 ≤ 132667424987^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21338933 100000000 132667424987 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597271459/5000000000 : ℝ)^17 ≤ (42464248538631/100000000000000 : ℝ)^13 := by
    have hnat : (2597271459 : ℕ)^17*100000000000000^13 ≤ 42464248538631^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597271459 5000000000 42464248538631 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072507729/2000000000 : ℝ), (-21338933/100000000 : ℝ), (2597271459/5000000000 : ℝ)] ![(44269008949189/100000000000000 : ℝ), (132667424987/1000000000000 : ℝ), (42464248538631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072507729/2000000000 : ℝ)|^17 ≤ (44269008949189/100000000000000 : ℝ)^13
        have hw : |(1072507729/2000000000 : ℝ)|=(1072507729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21338933/100000000 : ℝ)|^17 ≤ (132667424987/1000000000000 : ℝ)^13
        have hw : |(-21338933/100000000 : ℝ)|=(21338933/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2597271459/5000000000 : ℝ)|^17 ≤ (42464248538631/100000000000000 : ℝ)^13
        have hw : |(2597271459/5000000000 : ℝ)|=(2597271459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2681269239/5000000000 : ℝ)*x 0 + (51945431/100000000 : ℝ)*x 1 + (-533473321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681269239/5000000000 : ℝ)^17 ≤ (44269007146373/100000000000000 : ℝ)^13 := by
    have hnat : (2681269239 : ℕ)^17*100000000000000^13 ≤ 44269007146373^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681269239 5000000000 44269007146373 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51945431/100000000 : ℝ)^17 ≤ (10616062621057/25000000000000 : ℝ)^13 := by
    have hnat : (51945431 : ℕ)^17*25000000000000^13 ≤ 10616062621057^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51945431 100000000 10616062621057 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533473321/2500000000 : ℝ)^17 ≤ (6633371184309/50000000000000 : ℝ)^13 := by
    have hnat : (533473321 : ℕ)^17*50000000000000^13 ≤ 6633371184309^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533473321 2500000000 6633371184309 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681269239/5000000000 : ℝ), (51945431/100000000 : ℝ), (-533473321/2500000000 : ℝ)] ![(44269007146373/100000000000000 : ℝ), (10616062621057/25000000000000 : ℝ), (6633371184309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681269239/5000000000 : ℝ)|^17 ≤ (44269007146373/100000000000000 : ℝ)^13
        have hw : |(2681269239/5000000000 : ℝ)|=(2681269239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(51945431/100000000 : ℝ)|^17 ≤ (10616062621057/25000000000000 : ℝ)^13
        have hw : |(51945431/100000000 : ℝ)|=(51945431/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-533473321/2500000000 : ℝ)|^17 ≤ (6633371184309/50000000000000 : ℝ)^13
        have hw : |(-533473321/2500000000 : ℝ)|=(533473321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4308644731/10000000000 : ℝ)*x 0 + (4027047529/10000000000 : ℝ)*x 1 + (4608109737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308644731/10000000000 : ℝ)^17 ≤ (33252946043089/100000000000000 : ℝ)^13 := by
    have hnat : (4308644731 : ℕ)^17*100000000000000^13 ≤ 33252946043089^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308644731 10000000000 33252946043089 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4027047529/10000000000 : ℝ)^17 ≤ (30439969893753/100000000000000 : ℝ)^13 := by
    have hnat : (4027047529 : ℕ)^17*100000000000000^13 ≤ 30439969893753^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027047529 10000000000 30439969893753 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4608109737/10000000000 : ℝ)^17 ≤ (4538385505871/12500000000000 : ℝ)^13 := by
    have hnat : (4608109737 : ℕ)^17*12500000000000^13 ≤ 4538385505871^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4608109737 10000000000 4538385505871 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308644731/10000000000 : ℝ), (4027047529/10000000000 : ℝ), (4608109737/10000000000 : ℝ)] ![(33252946043089/100000000000000 : ℝ), (30439969893753/100000000000000 : ℝ), (4538385505871/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308644731/10000000000 : ℝ)|^17 ≤ (33252946043089/100000000000000 : ℝ)^13
        have hw : |(4308644731/10000000000 : ℝ)|=(4308644731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4027047529/10000000000 : ℝ)|^17 ≤ (30439969893753/100000000000000 : ℝ)^13
        have hw : |(4027047529/10000000000 : ℝ)|=(4027047529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4608109737/10000000000 : ℝ)|^17 ≤ (4538385505871/12500000000000 : ℝ)^13
        have hw : |(4608109737/10000000000 : ℝ)|=(4608109737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-99680917/500000000 : ℝ)*x 0 + (2598080589/5000000000 : ℝ)*x 1 + (5465193401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99680917/500000000 : ℝ)^17 ≤ (12138003467441/100000000000000 : ℝ)^13 := by
    have hnat : (99680917 : ℕ)^17*100000000000000^13 ≤ 12138003467441^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99680917 500000000 12138003467441 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598080589/5000000000 : ℝ)^17 ≤ (42481548725153/100000000000000 : ℝ)^13 := by
    have hnat : (2598080589 : ℕ)^17*100000000000000^13 ≤ 42481548725153^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598080589 5000000000 42481548725153 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465193401/10000000000 : ℝ)^17 ≤ (22690223891663/50000000000000 : ℝ)^13 := by
    have hnat : (5465193401 : ℕ)^17*50000000000000^13 ≤ 22690223891663^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465193401 10000000000 22690223891663 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99680917/500000000 : ℝ), (2598080589/5000000000 : ℝ), (5465193401/10000000000 : ℝ)] ![(12138003467441/100000000000000 : ℝ), (42481548725153/100000000000000 : ℝ), (22690223891663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99680917/500000000 : ℝ)|^17 ≤ (12138003467441/100000000000000 : ℝ)^13
        have hw : |(-99680917/500000000 : ℝ)|=(99680917/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598080589/5000000000 : ℝ)|^17 ≤ (42481548725153/100000000000000 : ℝ)^13
        have hw : |(2598080589/5000000000 : ℝ)|=(2598080589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465193401/10000000000 : ℝ)|^17 ≤ (22690223891663/50000000000000 : ℝ)^13
        have hw : |(5465193401/10000000000 : ℝ)|=(5465193401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5291990311/10000000000 : ℝ)*x 0 + (-232905431/1250000000 : ℝ)*x 1 + (5465193089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291990311/10000000000 : ℝ)^17 ≤ (43508964276139/100000000000000 : ℝ)^13 := by
    have hnat : (5291990311 : ℕ)^17*100000000000000^13 ≤ 43508964276139^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291990311 10000000000 43508964276139 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232905431/1250000000 : ℝ)^17 ≤ (555529565403/5000000000000 : ℝ)^13 := by
    have hnat : (232905431 : ℕ)^17*5000000000000^13 ≤ 555529565403^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232905431 1250000000 555529565403 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465193089/10000000000 : ℝ)^17 ≤ (22690222197741/50000000000000 : ℝ)^13 := by
    have hnat : (5465193089 : ℕ)^17*50000000000000^13 ≤ 22690222197741^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465193089 10000000000 22690222197741 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291990311/10000000000 : ℝ), (-232905431/1250000000 : ℝ), (5465193089/10000000000 : ℝ)] ![(43508964276139/100000000000000 : ℝ), (555529565403/5000000000000 : ℝ), (22690222197741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291990311/10000000000 : ℝ)|^17 ≤ (43508964276139/100000000000000 : ℝ)^13
        have hw : |(5291990311/10000000000 : ℝ)|=(5291990311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-232905431/1250000000 : ℝ)|^17 ≤ (555529565403/5000000000000 : ℝ)^13
        have hw : |(-232905431/1250000000 : ℝ)|=(232905431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465193089/10000000000 : ℝ)|^17 ≤ (22690222197741/50000000000000 : ℝ)^13
        have hw : |(5465193089/10000000000 : ℝ)|=(5465193089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (82687371/156250000 : ℝ)*x 0 + (2732596549/5000000000 : ℝ)*x 1 + (-1863241461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82687371/156250000 : ℝ)^17 ≤ (8701795936581/20000000000000 : ℝ)^13 := by
    have hnat : (82687371 : ℕ)^17*20000000000000^13 ≤ 8701795936581^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82687371 156250000 8701795936581 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732596549/5000000000 : ℝ)^17 ≤ (45380444493209/100000000000000 : ℝ)^13 := by
    have hnat : (2732596549 : ℕ)^17*100000000000000^13 ≤ 45380444493209^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732596549 5000000000 45380444493209 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863241461/10000000000 : ℝ)^17 ≤ (11110575813797/100000000000000 : ℝ)^13 := by
    have hnat : (1863241461 : ℕ)^17*100000000000000^13 ≤ 11110575813797^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863241461 10000000000 11110575813797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82687371/156250000 : ℝ), (2732596549/5000000000 : ℝ), (-1863241461/10000000000 : ℝ)] ![(8701795936581/20000000000000 : ℝ), (45380444493209/100000000000000 : ℝ), (11110575813797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82687371/156250000 : ℝ)|^17 ≤ (8701795936581/20000000000000 : ℝ)^13
        have hw : |(82687371/156250000 : ℝ)|=(82687371/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732596549/5000000000 : ℝ)|^17 ≤ (45380444493209/100000000000000 : ℝ)^13
        have hw : |(2732596549/5000000000 : ℝ)|=(2732596549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1863241461/10000000000 : ℝ)|^17 ≤ (11110575813797/100000000000000 : ℝ)^13
        have hw : |(-1863241461/10000000000 : ℝ)|=(1863241461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s2_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4308758703/10000000000 : ℝ)*x 0 + (2302328461/5000000000 : ℝ)*x 1 + (806105861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308758703/10000000000 : ℝ)^17 ≤ (6650819260051/20000000000000 : ℝ)^13 := by
    have hnat : (4308758703 : ℕ)^17*20000000000000^13 ≤ 6650819260051^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308758703 10000000000 6650819260051 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2302328461/5000000000 : ℝ)^17 ≤ (7254302588313/20000000000000 : ℝ)^13 := by
    have hnat : (2302328461 : ℕ)^17*20000000000000^13 ≤ 7254302588313^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302328461 5000000000 7254302588313 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806105861/2000000000 : ℝ)^17 ≤ (15237195372717/50000000000000 : ℝ)^13 := by
    have hnat : (806105861 : ℕ)^17*50000000000000^13 ≤ 15237195372717^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806105861 2000000000 15237195372717 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308758703/10000000000 : ℝ), (2302328461/5000000000 : ℝ), (806105861/2000000000 : ℝ)] ![(6650819260051/20000000000000 : ℝ), (7254302588313/20000000000000 : ℝ), (15237195372717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308758703/10000000000 : ℝ)|^17 ≤ (6650819260051/20000000000000 : ℝ)^13
        have hw : |(4308758703/10000000000 : ℝ)|=(4308758703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2302328461/5000000000 : ℝ)|^17 ≤ (7254302588313/20000000000000 : ℝ)^13
        have hw : |(2302328461/5000000000 : ℝ)|=(2302328461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806105861/2000000000 : ℝ)|^17 ≤ (15237195372717/50000000000000 : ℝ)^13
        have hw : |(806105861/2000000000 : ℝ)|=(806105861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10161/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (199/1250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19099/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19099/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19099/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7339/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (1513786225803189/100000000000000000000 : ℝ) := by
    have hpowers : (7339/100000 : ℝ)^4351 ≤ (1513786225803189/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7339 : ℕ)^4351*100000000000000000000^1024 ≤ 1513786225803189^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 100000 1513786225803189 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/100000 : ℝ)) (X := (1513786225803189/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19099/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (88104341610075927/100000000000000000000 : ℝ) := by
    have hpowers : (19099/100000 : ℝ)^4351 ≤ (88104341610075927/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19099 : ℕ)^4351*100000000000000000000^1024 ≤ 88104341610075927^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19099 100000 88104341610075927 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19099/100000 : ℝ)) (X := (88104341610075927/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001513786225803189/50000000000000000000 : ℝ) ≤ (10000071252546663/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50001513786225803189/50000000000000000000 : ℝ)^1024 ≤ (10000071252546663/10000000000000000 : ℝ)^4351 := by
      have hnat : (50001513786225803189 : ℕ)^1024*10000000000000000^4351 ≤ 10000071252546663^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001513786225803189 50000000000000000000 10000071252546663 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000071252546663/10000000000000000 : ℝ)) (X := (50001513786225803189/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25022404531958969779/25000000000000000000 : ℝ) ≤ (625131776511671/625000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (25022404531958969779/25000000000000000000 : ℝ)^1024 ≤ (625131776511671/625000000000000 : ℝ)^4351 := by
      have hnat : (25022404531958969779 : ℕ)^1024*625000000000000^4351 ≤ 625131776511671^4351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022404531958969779 25000000000000000000 625131776511671 625000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625131776511671/625000000000000 : ℝ)) (X := (25022404531958969779/25000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50088104341610075927/50000000000000000000 : ℝ) ≤ (10004145595826809/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50088104341610075927/50000000000000000000 : ℝ)^1024 ≤ (10004145595826809/10000000000000000 : ℝ)^4351 := by
      have hnat : (50088104341610075927 : ℕ)^1024*10000000000000000^4351 ≤ 10004145595826809^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50088104341610075927 50000000000000000000 10004145595826809 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004145595826809/10000000000000000 : ℝ)) (X := (50088104341610075927/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1513786225803189/100000000000000000000 : ℝ) ≤ ((58785468162307882693/58800000000000000000 : ℝ)+2*(2037171640073/1176000000000000 : ℝ)*(7339/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (58785468162307882693/58800000000000000000 : ℝ)+2*(2037171640073/1176000000000000 : ℝ)*(7339/100000 : ℝ)=(10000071252546663/10000000000000000 : ℝ) by norm_num, show 1+2*(1513786225803189/100000000000000000000 : ℝ)=(50001513786225803189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(88104341610075927/100000000000000000000 : ℝ)+(1513786225803189/100000000000000000000 : ℝ) ≤ ((58785468162307882693/58800000000000000000 : ℝ)+(2037171640073/1176000000000000 : ℝ)*((19099/100000 : ℝ)+(7339/100000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (58785468162307882693/58800000000000000000 : ℝ)+(2037171640073/1176000000000000 : ℝ)*((19099/100000 : ℝ)+(7339/100000 : ℝ))=(625131776511671/625000000000000 : ℝ) by norm_num, show 1+(88104341610075927/100000000000000000000 : ℝ)+(1513786225803189/100000000000000000000 : ℝ)=(25022404531958969779/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(88104341610075927/100000000000000000000 : ℝ) ≤ ((58785468162307882693/58800000000000000000 : ℝ)+2*(2037171640073/1176000000000000 : ℝ)*(19099/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (58785468162307882693/58800000000000000000 : ℝ)+2*(2037171640073/1176000000000000 : ℝ)*(19099/100000 : ℝ)=(10004145595826809/10000000000000000 : ℝ) by norm_num, show 1+2*(88104341610075927/100000000000000000000 : ℝ)=(50088104341610075927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58785468162307882693/58800000000000000000 : ℝ)*(X 1 0+X 2 0)+(2037171640073/1176000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (7339/100000 : ℝ)) (hi := (19099/100000 : ℝ)) (c := (58785468162307882693/58800000000000000000 : ℝ)) (alpha := (2037171640073/1176000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58785468162307882693/58800000000000000000 : ℝ)*(X 0 1+X 2 1)+(2037171640073/1176000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (7339/100000 : ℝ)) (hi := (19099/100000 : ℝ)) (c := (58785468162307882693/58800000000000000000 : ℝ)) (alpha := (2037171640073/1176000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58785468162307882693/58800000000000000000 : ℝ)*(X 0 2+X 1 2)+(2037171640073/1176000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (7339/100000 : ℝ)) (hi := (19099/100000 : ℝ)) (c := (58785468162307882693/58800000000000000000 : ℝ)) (alpha := (2037171640073/1176000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-249195699/1250000000 : ℝ)*X 0 0+(5466825199/10000000000 : ℝ)*X 0 1+(2597271483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1072507729/2000000000 : ℝ)*X 1 0+(-21338933/100000000 : ℝ)*X 1 1+(2597271459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681269239/5000000000 : ℝ)*X 2 0+(51945431/100000000 : ℝ)*X 2 1+(-533473321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308644731/10000000000 : ℝ)*X 0 0+(4027047529/10000000000 : ℝ)*X 0 1+(4608109737/10000000000 : ℝ)*X 0 2+(4308644731/10000000000 : ℝ)*X 1 0+(4027047529/10000000000 : ℝ)*X 1 1+(4608109737/10000000000 : ℝ)*X 1 2+(4308644731/10000000000 : ℝ)*X 2 0+(4027047529/10000000000 : ℝ)*X 2 1+(4608109737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-99680917/500000000 : ℝ)*X 0 0+(2598080589/5000000000 : ℝ)*X 0 1+(5465193401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291990311/10000000000 : ℝ)*X 1 0+(-232905431/1250000000 : ℝ)*X 1 1+(5465193089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82687371/156250000 : ℝ)*X 2 0+(2732596549/5000000000 : ℝ)*X 2 1+(-1863241461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308758703/10000000000 : ℝ)*X 0 0+(2302328461/5000000000 : ℝ)*X 0 1+(806105861/2000000000 : ℝ)*X 0 2+(4308758703/10000000000 : ℝ)*X 1 0+(2302328461/5000000000 : ℝ)*X 1 1+(806105861/2000000000 : ℝ)*X 1 2+(4308758703/10000000000 : ℝ)*X 2 0+(2302328461/5000000000 : ℝ)*X 2 1+(806105861/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (796902362212219891861505459/140000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1003413553/100000000000000 : ℝ)*(base19) + (766306251/100000000000000 : ℝ)*(base23) + (32907961/50000000000000 : ℝ)*(lower2) + (46313783/25000000000000 : ℝ)*(upper3) + (77731447/100000000000000 : ℝ)*(upper5) + (2696840256524641/100000000000000 : ℝ)*(major0) + (2696840256524641/100000000000000 : ℝ)*(major1) + (2696840256524641/100000000000000 : ℝ)*(major2) + (459084021733273/12500000000000 : ℝ)*(sp0) + (1836340745056743/50000000000000 : ℝ)*(sp1) + (918170431805197/25000000000000 : ℝ)*(sp2) + (344198280111711/20000000000000 : ℝ)*(sp3) + (1289957607/12500000000000 : ℝ)*(sp4) + (6429225023/100000000000000 : ℝ)*(sp7) + (860498914891789/50000000000000 : ℝ)*(f.failure) + (717320799517/19531250000 : ℝ)*(f.sum) + (87667936134007/58800000000000000000000000000 : ℝ)*base66 + (34640099219568411787/5880000000000000000000000000000000 : ℝ)*base68 + (78672968817768411787/5880000000000000000000000000000000 : ℝ)*base70 + (22952285386488411787/5880000000000000000000000000000000 : ℝ)*base72 + (126015361320007/58800000000000000000000000000 : ℝ)*base74 + (39950626591991588213/5880000000000000000000000000000000 : ℝ)*base75 + (32012272847208411787/5880000000000000000000000000000000 : ℝ)*base78 + (9675439142351588213/5880000000000000000000000000000000 : ℝ)*base79 + (85236694431607/58800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (581057/500000000000000000000 : ℝ)*base89 + (581057/500000000000000000000 : ℝ)*base91 + (581057/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89970584031622104976957/9800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1415873249/100000000000000 : ℝ)*(base19) + (144590821/4000000000000 : ℝ)*(base23) + (294491073/100000000000000 : ℝ)*(upper3) + (10441521/3125000000000 : ℝ)*(lower4) + (26135653/25000000000000 : ℝ)*(upper5) + (1364700439430491/50000000000000 : ℝ)*(major0) + (1364700439430491/50000000000000 : ℝ)*(major1) + (1364700439430491/50000000000000 : ℝ)*(major2) + (4278750819/50000000000000 : ℝ)*(sp1) + (12659984633/25000000000000 : ℝ)*(sp2) + (929256237363071/25000000000000 : ℝ)*(sp4) + (929253744019349/25000000000000 : ℝ)*(sp5) + (929242673685807/25000000000000 : ℝ)*(sp6) + (870888251123639/50000000000000 : ℝ)*(sp7) + (870888251123639/50000000000000 : ℝ)*(f.failure) + (929256237363071/25000000000000 : ℝ)*(f.sum) + (98132360570243/29400000000000000000000000000 : ℝ)*base65 + (16441687903672457737/2940000000000000000000000000000000 : ℝ)*base68 + (1848725926687542263/2940000000000000000000000000000000 : ℝ)*base69 + (25822040334247542263/2940000000000000000000000000000000 : ℝ)*base71 + (210272452669357/29400000000000000000000000000 : ℝ)*base74 + (21507218077327542263/2940000000000000000000000000000000 : ℝ)*base75 + (13388249456032457737/2940000000000000000000000000000000 : ℝ)*base78 + (16113404540152457737/2940000000000000000000000000000000 : ℝ)*base80 + (163811527802243/29400000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2465107/500000000000000000000 : ℝ)*base89 + (2465107/500000000000000000000 : ℝ)*base91 + (2465107/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19099/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (199/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1392_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (199/1250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1392_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1392_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1392_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10161/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (199/1250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
