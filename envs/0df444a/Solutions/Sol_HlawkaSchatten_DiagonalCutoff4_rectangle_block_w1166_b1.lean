-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1166_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:42:31.595324+00:00
-- url     : https://prove2.me/submissions/eb5ca688-1d9a-49c1-bdc1-b74ad34ba000

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
theorem support_rectangle_w1166_s3_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151913329/10000000000 : ℝ)*x 0 + (2713373363/5000000000 : ℝ)*x 1 + (5234294877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151913329/10000000000 : ℝ)^8359 ≤ (653563679963/5000000000000 : ℝ)^6311 := by
    have hnat : (2151913329 : ℕ)^8359*5000000000000^6311 ≤ 653563679963^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151913329 10000000000 653563679963 5000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713373363/5000000000 : ℝ)^8359 ≤ (22251754309849/50000000000000 : ℝ)^6311 := by
    have hnat : (2713373363 : ℕ)^8359*50000000000000^6311 ≤ 22251754309849^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713373363 5000000000 22251754309849 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234294877/10000000000 : ℝ)^8359 ≤ (21212608883863/50000000000000 : ℝ)^6311 := by
    have hnat : (5234294877 : ℕ)^8359*50000000000000^6311 ≤ 21212608883863^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234294877 10000000000 21212608883863 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151913329/10000000000 : ℝ), (2713373363/5000000000 : ℝ), (5234294877/10000000000 : ℝ)] ![(653563679963/5000000000000 : ℝ), (22251754309849/50000000000000 : ℝ), (21212608883863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151913329/10000000000 : ℝ)|^8359 ≤ (653563679963/5000000000000 : ℝ)^6311
        have hw : |(-2151913329/10000000000 : ℝ)|=(2151913329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713373363/5000000000 : ℝ)|^8359 ≤ (22251754309849/50000000000000 : ℝ)^6311
        have hw : |(2713373363/5000000000 : ℝ)|=(2713373363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234294877/10000000000 : ℝ)|^8359 ≤ (21212608883863/50000000000000 : ℝ)^6311
        have hw : |(5234294877/10000000000 : ℝ)|=(5234294877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1070644471/2000000000 : ℝ)*x 0 + (-225023737/1000000000 : ℝ)*x 1 + (2617147341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070644471/2000000000 : ℝ)^8359 ≤ (8741329201361/20000000000000 : ℝ)^6311 := by
    have hnat : (1070644471 : ℕ)^8359*20000000000000^6311 ≤ 8741329201361^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070644471 2000000000 8741329201361 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225023737/1000000000 : ℝ)^8359 ≤ (6934069152033/50000000000000 : ℝ)^6311 := by
    have hnat : (225023737 : ℕ)^8359*50000000000000^6311 ≤ 6934069152033^6311*1000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225023737 1000000000 6934069152033 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617147341/5000000000 : ℝ)^8359 ≤ (8485043134861/20000000000000 : ℝ)^6311 := by
    have hnat : (2617147341 : ℕ)^8359*20000000000000^6311 ≤ 8485043134861^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617147341 5000000000 8485043134861 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070644471/2000000000 : ℝ), (-225023737/1000000000 : ℝ), (2617147341/5000000000 : ℝ)] ![(8741329201361/20000000000000 : ℝ), (6934069152033/50000000000000 : ℝ), (8485043134861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070644471/2000000000 : ℝ)|^8359 ≤ (8741329201361/20000000000000 : ℝ)^6311
        have hw : |(1070644471/2000000000 : ℝ)|=(1070644471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225023737/1000000000 : ℝ)|^8359 ≤ (6934069152033/50000000000000 : ℝ)^6311
        have hw : |(-225023737/1000000000 : ℝ)|=(225023737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617147341/5000000000 : ℝ)|^8359 ≤ (8485043134861/20000000000000 : ℝ)^6311
        have hw : |(2617147341/5000000000 : ℝ)|=(2617147341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353222437/10000000000 : ℝ)*x 0 + (5234294693/10000000000 : ℝ)*x 1 + (-1125118623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353222437/10000000000 : ℝ)^8359 ≤ (43706646893557/100000000000000 : ℝ)^6311 := by
    have hnat : (5353222437 : ℕ)^8359*100000000000000^6311 ≤ 43706646893557^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353222437 10000000000 43706646893557 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5234294693/10000000000 : ℝ)^8359 ≤ (8485043158479/20000000000000 : ℝ)^6311 := by
    have hnat : (5234294693 : ℕ)^8359*20000000000000^6311 ≤ 8485043158479^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234294693 10000000000 8485043158479 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125118623/5000000000 : ℝ)^8359 ≤ (13868137291863/100000000000000 : ℝ)^6311 := by
    have hnat : (1125118623 : ℕ)^8359*100000000000000^6311 ≤ 13868137291863^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125118623 5000000000 13868137291863 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353222437/10000000000 : ℝ), (5234294693/10000000000 : ℝ), (-1125118623/5000000000 : ℝ)] ![(43706646893557/100000000000000 : ℝ), (8485043158479/20000000000000 : ℝ), (13868137291863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353222437/10000000000 : ℝ)|^8359 ≤ (43706646893557/100000000000000 : ℝ)^6311
        have hw : |(5353222437/10000000000 : ℝ)|=(5353222437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5234294693/10000000000 : ℝ)|^8359 ≤ (8485043158479/20000000000000 : ℝ)^6311
        have hw : |(5234294693/10000000000 : ℝ)|=(5234294693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125118623/5000000000 : ℝ)|^8359 ≤ (13868137291863/100000000000000 : ℝ)^6311
        have hw : |(-1125118623/5000000000 : ℝ)|=(1125118623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359194557/10000000000 : ℝ)*x 0 + (4171047357/10000000000 : ℝ)*x 1 + (4555728553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359194557/10000000000 : ℝ)^8359 ≤ (16647881901961/50000000000000 : ℝ)^6311 := by
    have hnat : (4359194557 : ℕ)^8359*50000000000000^6311 ≤ 16647881901961^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359194557 10000000000 16647881901961 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171047357/10000000000 : ℝ)^8359 ≤ (31405796947723/100000000000000 : ℝ)^6311 := by
    have hnat : (4171047357 : ℕ)^8359*100000000000000^6311 ≤ 31405796947723^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171047357 10000000000 31405796947723 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4555728553/10000000000 : ℝ)^8359 ≤ (8824609808331/25000000000000 : ℝ)^6311 := by
    have hnat : (4555728553 : ℕ)^8359*25000000000000^6311 ≤ 8824609808331^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555728553 10000000000 8824609808331 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359194557/10000000000 : ℝ), (4171047357/10000000000 : ℝ), (4555728553/10000000000 : ℝ)] ![(16647881901961/50000000000000 : ℝ), (31405796947723/100000000000000 : ℝ), (8824609808331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359194557/10000000000 : ℝ)|^8359 ≤ (16647881901961/50000000000000 : ℝ)^6311
        have hw : |(4359194557/10000000000 : ℝ)|=(4359194557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171047357/10000000000 : ℝ)|^8359 ≤ (31405796947723/100000000000000 : ℝ)^6311
        have hw : |(4171047357/10000000000 : ℝ)|=(4171047357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4555728553/10000000000 : ℝ)|^8359 ≤ (8824609808331/25000000000000 : ℝ)^6311
        have hw : |(4555728553/10000000000 : ℝ)|=(4555728553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151930299/10000000000 : ℝ)*x 0 + (209401177/400000000 : ℝ)*x 1 + (1356502033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151930299/10000000000 : ℝ)^8359 ≤ (6535705065193/50000000000000 : ℝ)^6311 := by
    have hnat : (2151930299 : ℕ)^8359*50000000000000^6311 ≤ 6535705065193^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151930299 10000000000 6535705065193 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209401177/400000000 : ℝ)^8359 ≤ (10608275920761/25000000000000 : ℝ)^6311 := by
    have hnat : (209401177 : ℕ)^8359*25000000000000^6311 ≤ 10608275920761^6311*400000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209401177 400000000 10608275920761 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356502033/2500000000 : ℝ)^8359 ≤ (44495486169531/100000000000000 : ℝ)^6311 := by
    have hnat : (1356502033 : ℕ)^8359*100000000000000^6311 ≤ 44495486169531^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356502033 2500000000 44495486169531 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151930299/10000000000 : ℝ), (209401177/400000000 : ℝ), (1356502033/2500000000 : ℝ)] ![(6535705065193/50000000000000 : ℝ), (10608275920761/25000000000000 : ℝ), (44495486169531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151930299/10000000000 : ℝ)|^8359 ≤ (6535705065193/50000000000000 : ℝ)^6311
        have hw : |(-2151930299/10000000000 : ℝ)|=(2151930299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209401177/400000000 : ℝ)|^8359 ≤ (10608275920761/25000000000000 : ℝ)^6311
        have hw : |(209401177/400000000 : ℝ)|=(209401177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356502033/2500000000 : ℝ)|^8359 ≤ (44495486169531/100000000000000 : ℝ)^6311
        have hw : |(1356502033/2500000000 : ℝ)|=(1356502033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060876167/2000000000 : ℝ)*x 0 + (-205852391/1000000000 : ℝ)*x 1 + (2713004061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060876167/2000000000 : ℝ)^8359 ≤ (2698703432537/6250000000000 : ℝ)^6311 := by
    have hnat : (1060876167 : ℕ)^8359*6250000000000^6311 ≤ 2698703432537^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060876167 2000000000 2698703432537 6250000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205852391/1000000000 : ℝ)^8359 ≤ (12325259007331/100000000000000 : ℝ)^6311 := by
    have hnat : (205852391 : ℕ)^8359*100000000000000^6311 ≤ 12325259007331^6311*1000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205852391 1000000000 12325259007331 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713004061/5000000000 : ℝ)^8359 ≤ (11123871515229/25000000000000 : ℝ)^6311 := by
    have hnat : (2713004061 : ℕ)^8359*25000000000000^6311 ≤ 11123871515229^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713004061 5000000000 11123871515229 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060876167/2000000000 : ℝ), (-205852391/1000000000 : ℝ), (2713004061/5000000000 : ℝ)] ![(2698703432537/6250000000000 : ℝ), (12325259007331/100000000000000 : ℝ), (11123871515229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060876167/2000000000 : ℝ)|^8359 ≤ (2698703432537/6250000000000 : ℝ)^6311
        have hw : |(1060876167/2000000000 : ℝ)|=(1060876167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205852391/1000000000 : ℝ)|^8359 ≤ (12325259007331/100000000000000 : ℝ)^6311
        have hw : |(-205852391/1000000000 : ℝ)|=(205852391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713004061/5000000000 : ℝ)|^8359 ≤ (11123871515229/25000000000000 : ℝ)^6311
        have hw : |(2713004061/5000000000 : ℝ)|=(2713004061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652190359/5000000000 : ℝ)*x 0 + (1085201667/2000000000 : ℝ)*x 1 + (-2058523777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652190359/5000000000 : ℝ)^8359 ≤ (21589626829553/50000000000000 : ℝ)^6311 := by
    have hnat : (2652190359 : ℕ)^8359*50000000000000^6311 ≤ 21589626829553^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652190359 5000000000 21589626829553 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085201667/2000000000 : ℝ)^8359 ≤ (1779819534977/4000000000000 : ℝ)^6311 := by
    have hnat : (1085201667 : ℕ)^8359*4000000000000^6311 ≤ 1779819534977^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085201667 2000000000 1779819534977 4000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058523777/10000000000 : ℝ)^8359 ≤ (2465051590517/20000000000000 : ℝ)^6311 := by
    have hnat : (2058523777 : ℕ)^8359*20000000000000^6311 ≤ 2465051590517^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058523777 10000000000 2465051590517 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652190359/5000000000 : ℝ), (1085201667/2000000000 : ℝ), (-2058523777/10000000000 : ℝ)] ![(21589626829553/50000000000000 : ℝ), (1779819534977/4000000000000 : ℝ), (2465051590517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652190359/5000000000 : ℝ)|^8359 ≤ (21589626829553/50000000000000 : ℝ)^6311
        have hw : |(2652190359/5000000000 : ℝ)|=(2652190359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085201667/2000000000 : ℝ)|^8359 ≤ (1779819534977/4000000000000 : ℝ)^6311
        have hw : |(1085201667/2000000000 : ℝ)|=(1085201667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058523777/10000000000 : ℝ)|^8359 ≤ (2465051590517/20000000000000 : ℝ)^6311
        have hw : |(-2058523777/10000000000 : ℝ)|=(2058523777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s3_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272451781/625000000 : ℝ)*x 0 + (4554260249/10000000000 : ℝ)*x 1 + (4172523711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272451781/625000000 : ℝ)^8359 ≤ (33296107155039/100000000000000 : ℝ)^6311 := by
    have hnat : (272451781 : ℕ)^8359*100000000000000^6311 ≤ 33296107155039^6311*625000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272451781 625000000 33296107155039 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4554260249/10000000000 : ℝ)^8359 ≤ (35283371529433/100000000000000 : ℝ)^6311 := by
    have hnat : (4554260249 : ℕ)^8359*100000000000000^6311 ≤ 35283371529433^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554260249 10000000000 35283371529433 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172523711/10000000000 : ℝ)^8359 ≤ (15710260651489/50000000000000 : ℝ)^6311 := by
    have hnat : (4172523711 : ℕ)^8359*50000000000000^6311 ≤ 15710260651489^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172523711 10000000000 15710260651489 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272451781/625000000 : ℝ), (4554260249/10000000000 : ℝ), (4172523711/10000000000 : ℝ)] ![(33296107155039/100000000000000 : ℝ), (35283371529433/100000000000000 : ℝ), (15710260651489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272451781/625000000 : ℝ)|^8359 ≤ (33296107155039/100000000000000 : ℝ)^6311
        have hw : |(272451781/625000000 : ℝ)|=(272451781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4554260249/10000000000 : ℝ)|^8359 ≤ (35283371529433/100000000000000 : ℝ)^6311
        have hw : |(4554260249/10000000000 : ℝ)|=(4554260249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172523711/10000000000 : ℝ)|^8359 ≤ (15710260651489/50000000000000 : ℝ)^6311
        have hw : |(4172523711/10000000000 : ℝ)|=(4172523711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2141/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7389/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1027/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1027/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4589/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1027/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1027/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4589/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1027/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1027/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4589/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4589/50000 : ℝ) ^ (4179/1024 : ℝ) ≤ (1461699470746443/25000000000000000000 : ℝ) := by
    have hpowers : (4589/50000 : ℝ)^4179 ≤ (1461699470746443/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4589 : ℕ)^4179*25000000000000000000^1024 ≤ 1461699470746443^1024*50000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4589 50000 1461699470746443 25000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4589/50000 : ℝ)) (X := (1461699470746443/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1027/6250 : ℝ) ^ (4179/1024 : ℝ) ≤ (12595625320102731/20000000000000000000 : ℝ) := by
    have hpowers : (1027/6250 : ℝ)^4179 ≤ (12595625320102731/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1027 : ℕ)^4179*20000000000000000000^1024 ≤ 12595625320102731^1024*6250^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1027 6250 12595625320102731 20000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1027/6250 : ℝ)) (X := (12595625320102731/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501461699470746443/12500000000000000000 : ℝ) ≤ (500014326051139/500000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (12501461699470746443/12500000000000000000 : ℝ)^1024 ≤ (500014326051139/500000000000000 : ℝ)^4179 := by
      have hnat : (12501461699470746443 : ℕ)^1024*500000000000000^4179 ≤ 500014326051139^4179*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501461699470746443 12500000000000000000 500014326051139 500000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014326051139/500000000000000 : ℝ)) (X := (12501461699470746443/12500000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100068824924483499427/100000000000000000000 : ℝ) ≤ (10001686011486851/10000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (100068824924483499427/100000000000000000000 : ℝ)^1024 ≤ (10001686011486851/10000000000000000 : ℝ)^4179 := by
      have hnat : (100068824924483499427 : ℕ)^1024*10000000000000000^4179 ≤ 10001686011486851^4179*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100068824924483499427 100000000000000000000 10001686011486851 10000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001686011486851/10000000000000000 : ℝ)) (X := (100068824924483499427/100000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10012595625320102731/10000000000000000000 : ℝ) ≤ (5001542750975461/5000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (10012595625320102731/10000000000000000000 : ℝ)^1024 ≤ (5001542750975461/5000000000000000 : ℝ)^4179 := by
      have hnat : (10012595625320102731 : ℕ)^1024*5000000000000000^4179 ≤ 5001542750975461^4179*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10012595625320102731 10000000000000000000 5001542750975461 5000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001542750975461/5000000000000000 : ℝ)) (X := (10012595625320102731/10000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1461699470746443/25000000000000000000 : ℝ) ≤ ((464848649849620249/465000000000000000 : ℝ)+2*(466496821357/241800000000000 : ℝ)*(4589/50000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (464848649849620249/465000000000000000 : ℝ)+2*(466496821357/241800000000000 : ℝ)*(4589/50000 : ℝ)=(500014326051139/500000000000000 : ℝ) by norm_num, show 1+2*(1461699470746443/25000000000000000000 : ℝ)=(12501461699470746443/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12595625320102731/20000000000000000000 : ℝ)+(1461699470746443/25000000000000000000 : ℝ) ≤ ((464848649849620249/465000000000000000 : ℝ)+(466496821357/241800000000000 : ℝ)*((1027/6250 : ℝ)+(4589/50000 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (464848649849620249/465000000000000000 : ℝ)+(466496821357/241800000000000 : ℝ)*((1027/6250 : ℝ)+(4589/50000 : ℝ))=(10001686011486851/10000000000000000 : ℝ) by norm_num, show 1+(12595625320102731/20000000000000000000 : ℝ)+(1461699470746443/25000000000000000000 : ℝ)=(100068824924483499427/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12595625320102731/20000000000000000000 : ℝ) ≤ ((464848649849620249/465000000000000000 : ℝ)+2*(466496821357/241800000000000 : ℝ)*(1027/6250 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (464848649849620249/465000000000000000 : ℝ)+2*(466496821357/241800000000000 : ℝ)*(1027/6250 : ℝ)=(5001542750975461/5000000000000000 : ℝ) by norm_num, show 1+2*(12595625320102731/20000000000000000000 : ℝ)=(10012595625320102731/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (464848649849620249/465000000000000000 : ℝ)*(X 1 0+X 2 0)+(466496821357/241800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (4589/50000 : ℝ)) (hi := (1027/6250 : ℝ)) (c := (464848649849620249/465000000000000000 : ℝ)) (alpha := (466496821357/241800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (464848649849620249/465000000000000000 : ℝ)*(X 0 1+X 2 1)+(466496821357/241800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (4589/50000 : ℝ)) (hi := (1027/6250 : ℝ)) (c := (464848649849620249/465000000000000000 : ℝ)) (alpha := (466496821357/241800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (464848649849620249/465000000000000000 : ℝ)*(X 0 2+X 1 2)+(466496821357/241800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (4589/50000 : ℝ)) (hi := (1027/6250 : ℝ)) (c := (464848649849620249/465000000000000000 : ℝ)) (alpha := (466496821357/241800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2151913329/10000000000 : ℝ)*X 0 0+(2713373363/5000000000 : ℝ)*X 0 1+(5234294877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070644471/2000000000 : ℝ)*X 1 0+(-225023737/1000000000 : ℝ)*X 1 1+(2617147341/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353222437/10000000000 : ℝ)*X 2 0+(5234294693/10000000000 : ℝ)*X 2 1+(-1125118623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359194557/10000000000 : ℝ)*X 0 0+(4171047357/10000000000 : ℝ)*X 0 1+(4555728553/10000000000 : ℝ)*X 0 2+(4359194557/10000000000 : ℝ)*X 1 0+(4171047357/10000000000 : ℝ)*X 1 1+(4555728553/10000000000 : ℝ)*X 1 2+(4359194557/10000000000 : ℝ)*X 2 0+(4171047357/10000000000 : ℝ)*X 2 1+(4555728553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151930299/10000000000 : ℝ)*X 0 0+(209401177/400000000 : ℝ)*X 0 1+(1356502033/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060876167/2000000000 : ℝ)*X 1 0+(-205852391/1000000000 : ℝ)*X 1 1+(2713004061/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652190359/5000000000 : ℝ)*X 2 0+(1085201667/2000000000 : ℝ)*X 2 1+(-2058523777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272451781/625000000 : ℝ)*X 0 0+(4554260249/10000000000 : ℝ)*X 0 1+(4172523711/10000000000 : ℝ)*X 0 2+(272451781/625000000 : ℝ)*X 1 0+(4554260249/10000000000 : ℝ)*X 1 1+(4172523711/10000000000 : ℝ)*X 1 2+(272451781/625000000 : ℝ)*X 2 0+(4554260249/10000000000 : ℝ)*X 2 1+(4172523711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (325516626782952841868693559/50375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4950531/312500000000 : ℝ)*(base19) + (1528831277/100000000000000 : ℝ)*(base23) + (72232477/100000000000000 : ℝ)*(lower2) + (124775661/100000000000000 : ℝ)*(upper3) + (3403811/2000000000000 : ℝ)*(upper5) + (1948934434981431/50000000000000 : ℝ)*(major0) + (1948934434981431/50000000000000 : ℝ)*(major1) + (1948934434981431/50000000000000 : ℝ)*(major2) + (5196128864927151/100000000000000 : ℝ)*(sp0) + (2598077433582139/50000000000000 : ℝ)*(sp1) + (129903873062573/2500000000000 : ℝ)*(sp2) + (1299783998397721/50000000000000 : ℝ)*(sp3) + (27586407047/100000000000000 : ℝ)*(sp4) + (13076400453/100000000000000 : ℝ)*(sp7) + (324947634149487/12500000000000 : ℝ)*(f.failure) + (2598078225667099/50000000000000 : ℝ)*(f.sum) + (6273850030039/2015000000000000000000000000 : ℝ)*base65 + (1165871447026809049/100750000000000000000000000000000 : ℝ)*base67 + (1113264537515809049/100750000000000000000000000000000 : ℝ)*base69 + (1032075710991809049/100750000000000000000000000000000 : ℝ)*base71 + (1847456596081/503750000000000000000000000 : ℝ)*base73 + (547638122542059049/100750000000000000000000000000000 : ℝ)*base75 + (2130756339979309049/100750000000000000000000000000000 : ℝ)*base77 + (1524250485157559049/100750000000000000000000000000000 : ℝ)*base79 + (7198023478227/1007500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4395009/1250000000000000000000 : ℝ)*base90 + (4395009/1250000000000000000000 : ℝ)*base92 + (4395009/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (420321845695813707040986321/50375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69403099/4000000000000 : ℝ)*(base19) + (1845905531/100000000000000 : ℝ)*(base23) + (45594139/25000000000000 : ℝ)*(upper3) + (22702999/25000000000000 : ℝ)*(lower4) + (25311837/12500000000000 : ℝ)*(upper5) + (3927895667723967/100000000000000 : ℝ)*(major0) + (3927895667723967/100000000000000 : ℝ)*(major1) + (3927895667723967/100000000000000 : ℝ)*(major2) + (3161021411/10000000000000 : ℝ)*(sp1) + (37596516933/100000000000000 : ℝ)*(sp2) + (2618092200745163/50000000000000 : ℝ)*(sp4) + (261807552809937/5000000000000 : ℝ)*(sp5) + (2618072479533931/50000000000000 : ℝ)*(sp6) + (1309803327914501/50000000000000 : ℝ)*(sp7) + (1309803327914501/50000000000000 : ℝ)*(f.failure) + (2618092200745163/50000000000000 : ℝ)*(f.sum) + (6068357556467/4030000000000000000000000000 : ℝ)*base66 + (1060014921186674607/201500000000000000000000000000000 : ℝ)*base68 + (376717677504325393/201500000000000000000000000000000 : ℝ)*base69 + (386022849172325393/201500000000000000000000000000000 : ℝ)*base71 + (34995390792867/4030000000000000000000000000 : ℝ)*base74 + (3853560226502325393/201500000000000000000000000000000 : ℝ)*base75 + (217421011241825393/201500000000000000000000000000000 : ℝ)*base77 + (901320835329825393/201500000000000000000000000000000 : ℝ)*base79 + (15215537152827/4030000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (46440693/5000000000000000000000 : ℝ)*base89 + (46440693/5000000000000000000000 : ℝ)*base91 + (46440693/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1166_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2141/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1166_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1166_s4_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-67335279/312500000 : ℝ)*x 0 + (675095867/1250000000 : ℝ)*x 1 + (1314607967/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67335279/312500000 : ℝ)^8359 ≤ (6546965556191/50000000000000 : ℝ)^6311 := by
    have hnat : (67335279 : ℕ)^8359*50000000000000^6311 ≤ 6546965556191^6311*312500000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67335279 312500000 6546965556191 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675095867/1250000000 : ℝ)^8359 ≤ (8844306980019/20000000000000 : ℝ)^6311 := by
    have hnat : (675095867 : ℕ)^8359*20000000000000^6311 ≤ 8844306980019^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675095867 1250000000 8844306980019 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314607967/2500000000 : ℝ)^8359 ≤ (42684533972251/100000000000000 : ℝ)^6311 := by
    have hnat : (1314607967 : ℕ)^8359*100000000000000^6311 ≤ 42684533972251^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314607967 2500000000 42684533972251 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-67335279/312500000 : ℝ), (675095867/1250000000 : ℝ), (1314607967/2500000000 : ℝ)] ![(6546965556191/50000000000000 : ℝ), (8844306980019/20000000000000 : ℝ), (42684533972251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-67335279/312500000 : ℝ)|^8359 ≤ (6546965556191/50000000000000 : ℝ)^6311
        have hw : |(-67335279/312500000 : ℝ)|=(67335279/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675095867/1250000000 : ℝ)|^8359 ≤ (8844306980019/20000000000000 : ℝ)^6311
        have hw : |(675095867/1250000000 : ℝ)|=(675095867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314607967/2500000000 : ℝ)|^8359 ≤ (42684533972251/100000000000000 : ℝ)^6311
        have hw : |(1314607967/2500000000 : ℝ)|=(1314607967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673359583/5000000000 : ℝ)*x 0 + (-2227044027/10000000000 : ℝ)*x 1 + (2629216021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673359583/5000000000 : ℝ)^8359 ≤ (43636334066593/100000000000000 : ℝ)^6311 := by
    have hnat : (2673359583 : ℕ)^8359*100000000000000^6311 ≤ 43636334066593^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673359583 5000000000 43636334066593 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2227044027/10000000000 : ℝ)^8359 ≤ (1709891259271/12500000000000 : ℝ)^6311 := by
    have hnat : (2227044027 : ℕ)^8359*12500000000000^6311 ≤ 1709891259271^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227044027 10000000000 1709891259271 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629216021/5000000000 : ℝ)^8359 ≤ (21342267921509/50000000000000 : ℝ)^6311 := by
    have hnat : (2629216021 : ℕ)^8359*50000000000000^6311 ≤ 21342267921509^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629216021 5000000000 21342267921509 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673359583/5000000000 : ℝ), (-2227044027/10000000000 : ℝ), (2629216021/5000000000 : ℝ)] ![(43636334066593/100000000000000 : ℝ), (1709891259271/12500000000000 : ℝ), (21342267921509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673359583/5000000000 : ℝ)|^8359 ≤ (43636334066593/100000000000000 : ℝ)^6311
        have hw : |(2673359583/5000000000 : ℝ)|=(2673359583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2227044027/10000000000 : ℝ)|^8359 ≤ (1709891259271/12500000000000 : ℝ)^6311
        have hw : |(-2227044027/10000000000 : ℝ)|=(2227044027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629216021/5000000000 : ℝ)|^8359 ≤ (21342267921509/50000000000000 : ℝ)^6311
        have hw : |(2629216021/5000000000 : ℝ)|=(2629216021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346718713/10000000000 : ℝ)*x 0 + (2629216157/5000000000 : ℝ)*x 1 + (-2227044269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346718713/10000000000 : ℝ)^8359 ≤ (43636329169761/100000000000000 : ℝ)^6311 := by
    have hnat : (5346718713 : ℕ)^8359*100000000000000^6311 ≤ 43636329169761^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346718713 10000000000 43636329169761 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629216157/5000000000 : ℝ)^8359 ≤ (8536907753487/20000000000000 : ℝ)^6311 := by
    have hnat : (2629216157 : ℕ)^8359*20000000000000^6311 ≤ 8536907753487^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629216157 5000000000 8536907753487 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2227044269/10000000000 : ℝ)^8359 ≤ (6839566021483/50000000000000 : ℝ)^6311 := by
    have hnat : (2227044269 : ℕ)^8359*50000000000000^6311 ≤ 6839566021483^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227044269 10000000000 6839566021483 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346718713/10000000000 : ℝ), (2629216157/5000000000 : ℝ), (-2227044269/10000000000 : ℝ)] ![(43636329169761/100000000000000 : ℝ), (8536907753487/20000000000000 : ℝ), (6839566021483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346718713/10000000000 : ℝ)|^8359 ≤ (43636329169761/100000000000000 : ℝ)^6311
        have hw : |(5346718713/10000000000 : ℝ)|=(5346718713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629216157/5000000000 : ℝ)|^8359 ≤ (8536907753487/20000000000000 : ℝ)^6311
        have hw : |(2629216157/5000000000 : ℝ)|=(2629216157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2227044269/10000000000 : ℝ)|^8359 ≤ (6839566021483/50000000000000 : ℝ)^6311
        have hw : |(-2227044269/10000000000 : ℝ)|=(2227044269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360875577/10000000000 : ℝ)*x 0 + (52761481/125000000 : ℝ)*x 1 + (2252711767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360875577/10000000000 : ℝ)^8359 ≤ (33312771243069/100000000000000 : ℝ)^6311 := by
    have hnat : (4360875577 : ℕ)^8359*100000000000000^6311 ≤ 33312771243069^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360875577 10000000000 33312771243069 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52761481/125000000 : ℝ)^8359 ≤ (31904118259327/100000000000000 : ℝ)^6311 := by
    have hnat : (52761481 : ℕ)^8359*100000000000000^6311 ≤ 31904118259327^6311*125000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52761481 125000000 31904118259327 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252711767/5000000000 : ℝ)^8359 ≤ (543486101277/1562500000000 : ℝ)^6311 := by
    have hnat : (2252711767 : ℕ)^8359*1562500000000^6311 ≤ 543486101277^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252711767 5000000000 543486101277 1562500000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360875577/10000000000 : ℝ), (52761481/125000000 : ℝ), (2252711767/5000000000 : ℝ)] ![(33312771243069/100000000000000 : ℝ), (31904118259327/100000000000000 : ℝ), (543486101277/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360875577/10000000000 : ℝ)|^8359 ≤ (33312771243069/100000000000000 : ℝ)^6311
        have hw : |(4360875577/10000000000 : ℝ)|=(4360875577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52761481/125000000 : ℝ)|^8359 ≤ (31904118259327/100000000000000 : ℝ)^6311
        have hw : |(52761481/125000000 : ℝ)|=(52761481/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252711767/5000000000 : ℝ)|^8359 ≤ (543486101277/1562500000000 : ℝ)^6311
        have hw : |(2252711767/5000000000 : ℝ)|=(2252711767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2154735613/10000000000 : ℝ)*x 0 + (2629417261/5000000000 : ℝ)*x 1 + (2700181393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154735613/10000000000 : ℝ)^8359 ≤ (13093984918937/100000000000000 : ℝ)^6311 := by
    have hnat : (2154735613 : ℕ)^8359*100000000000000^6311 ≤ 13093984918937^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154735613 10000000000 13093984918937 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629417261/5000000000 : ℝ)^8359 ≤ (21344431587131/50000000000000 : ℝ)^6311 := by
    have hnat : (2629417261 : ℕ)^8359*50000000000000^6311 ≤ 21344431587131^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629417261 5000000000 21344431587131 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700181393/5000000000 : ℝ)^8359 ≤ (5527143987057/12500000000000 : ℝ)^6311 := by
    have hnat : (2700181393 : ℕ)^8359*12500000000000^6311 ≤ 5527143987057^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700181393 5000000000 5527143987057 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2154735613/10000000000 : ℝ), (2629417261/5000000000 : ℝ), (2700181393/5000000000 : ℝ)] ![(13093984918937/100000000000000 : ℝ), (21344431587131/50000000000000 : ℝ), (5527143987057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2154735613/10000000000 : ℝ)|^8359 ≤ (13093984918937/100000000000000 : ℝ)^6311
        have hw : |(-2154735613/10000000000 : ℝ)|=(2154735613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629417261/5000000000 : ℝ)|^8359 ≤ (21344431587131/50000000000000 : ℝ)^6311
        have hw : |(2629417261/5000000000 : ℝ)|=(2629417261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700181393/5000000000 : ℝ)|^8359 ≤ (5527143987057/12500000000000 : ℝ)^6311
        have hw : |(2700181393/5000000000 : ℝ)|=(2700181393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310596459/10000000000 : ℝ)*x 0 + (-2085113313/10000000000 : ℝ)*x 1 + (1350090677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310596459/10000000000 : ℝ)^8359 ≤ (21623142047467/50000000000000 : ℝ)^6311 := by
    have hnat : (5310596459 : ℕ)^8359*50000000000000^6311 ≤ 21623142047467^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310596459 10000000000 21623142047467 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085113313/10000000000 : ℝ)^8359 ≤ (12536564844493/100000000000000 : ℝ)^6311 := by
    have hnat : (2085113313 : ℕ)^8359*100000000000000^6311 ≤ 12536564844493^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085113313 10000000000 12536564844493 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350090677/2500000000 : ℝ)^8359 ≤ (44217151050557/100000000000000 : ℝ)^6311 := by
    have hnat : (1350090677 : ℕ)^8359*100000000000000^6311 ≤ 44217151050557^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350090677 2500000000 44217151050557 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310596459/10000000000 : ℝ), (-2085113313/10000000000 : ℝ), (1350090677/2500000000 : ℝ)] ![(21623142047467/50000000000000 : ℝ), (12536564844493/100000000000000 : ℝ), (44217151050557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310596459/10000000000 : ℝ)|^8359 ≤ (21623142047467/50000000000000 : ℝ)^6311
        have hw : |(5310596459/10000000000 : ℝ)|=(5310596459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2085113313/10000000000 : ℝ)|^8359 ≤ (12536564844493/100000000000000 : ℝ)^6311
        have hw : |(-2085113313/10000000000 : ℝ)|=(2085113313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350090677/2500000000 : ℝ)|^8359 ≤ (44217151050557/100000000000000 : ℝ)^6311
        have hw : |(1350090677/2500000000 : ℝ)|=(1350090677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310596303/10000000000 : ℝ)*x 0 + (5400362641/10000000000 : ℝ)*x 1 + (-417022723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310596303/10000000000 : ℝ)^8359 ≤ (43246282412313/100000000000000 : ℝ)^6311 := by
    have hnat : (5310596303 : ℕ)^8359*100000000000000^6311 ≤ 43246282412313^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310596303 10000000000 43246282412313 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400362641/10000000000 : ℝ)^8359 ≤ (44217150323951/100000000000000 : ℝ)^6311 := by
    have hnat : (5400362641 : ℕ)^8359*100000000000000^6311 ≤ 44217150323951^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400362641 10000000000 44217150323951 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417022723/2000000000 : ℝ)^8359 ≤ (3134141812369/25000000000000 : ℝ)^6311 := by
    have hnat : (417022723 : ℕ)^8359*25000000000000^6311 ≤ 3134141812369^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417022723 2000000000 3134141812369 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310596303/10000000000 : ℝ), (5400362641/10000000000 : ℝ), (-417022723/2000000000 : ℝ)] ![(43246282412313/100000000000000 : ℝ), (44217150323951/100000000000000 : ℝ), (3134141812369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310596303/10000000000 : ℝ)|^8359 ≤ (43246282412313/100000000000000 : ℝ)^6311
        have hw : |(5310596303/10000000000 : ℝ)|=(5310596303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400362641/10000000000 : ℝ)|^8359 ≤ (44217150323951/100000000000000 : ℝ)^6311
        have hw : |(5400362641/10000000000 : ℝ)|=(5400362641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417022723/2000000000 : ℝ)|^8359 ≤ (3134141812369/25000000000000 : ℝ)^6311
        have hw : |(-417022723/2000000000 : ℝ)|=(417022723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s4_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360889409/10000000000 : ℝ)*x 0 + (2252309343/5000000000 : ℝ)*x 1 + (2110863259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360889409/10000000000 : ℝ)^8359 ≤ (6662582238969/20000000000000 : ℝ)^6311 := by
    have hnat : (4360889409 : ℕ)^8359*20000000000000^6311 ≤ 6662582238969^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360889409 10000000000 6662582238969 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252309343/5000000000 : ℝ)^8359 ≤ (34774880663969/100000000000000 : ℝ)^6311 := by
    have hnat : (2252309343 : ℕ)^8359*100000000000000^6311 ≤ 34774880663969^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252309343 5000000000 34774880663969 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110863259/5000000000 : ℝ)^8359 ≤ (31912208122963/100000000000000 : ℝ)^6311 := by
    have hnat : (2110863259 : ℕ)^8359*100000000000000^6311 ≤ 31912208122963^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110863259 5000000000 31912208122963 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360889409/10000000000 : ℝ), (2252309343/5000000000 : ℝ), (2110863259/5000000000 : ℝ)] ![(6662582238969/20000000000000 : ℝ), (34774880663969/100000000000000 : ℝ), (31912208122963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360889409/10000000000 : ℝ)|^8359 ≤ (6662582238969/20000000000000 : ℝ)^6311
        have hw : |(4360889409/10000000000 : ℝ)|=(4360889409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252309343/5000000000 : ℝ)|^8359 ≤ (34774880663969/100000000000000 : ℝ)^6311
        have hw : |(2252309343/5000000000 : ℝ)|=(2252309343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110863259/5000000000 : ℝ)|^8359 ≤ (31912208122963/100000000000000 : ℝ)^6311
        have hw : |(2110863259/5000000000 : ℝ)|=(2110863259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2141/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (561/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2141/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2141/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2141/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7389/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2141/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2141/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7389/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2141/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2141/20000 : ℝ) ^ (4179/1024 : ℝ) ≤ (10956961545276541/100000000000000000000 : ℝ) := by
    have hpowers : (2141/20000 : ℝ)^4179 ≤ (10956961545276541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2141 : ℕ)^4179*100000000000000000000^1024 ≤ 10956961545276541^1024*20000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2141 20000 10956961545276541 100000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2141/20000 : ℝ)) (X := (10956961545276541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7389/50000 : ℝ) ^ (4179/1024 : ℝ) ≤ (326772945543031/800000000000000000 : ℝ) := by
    have hpowers : (7389/50000 : ℝ)^4179 ≤ (326772945543031/800000000000000000 : ℝ)^1024 := by
      have hnat : (7389 : ℕ)^4179*800000000000000000^1024 ≤ 326772945543031^1024*50000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7389 50000 326772945543031 800000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7389/50000 : ℝ)) (X := (326772945543031/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010956961545276541/50000000000000000000 : ℝ) ≤ (5000268461369101/5000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (50010956961545276541/50000000000000000000 : ℝ)^1024 ≤ (5000268461369101/5000000000000000 : ℝ)^4179 := by
      have hnat : (50010956961545276541 : ℕ)^1024*5000000000000000^4179 ≤ 5000268461369101^4179*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010956961545276541 50000000000000000000 5000268461369101 5000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268461369101/5000000000000000 : ℝ)) (X := (50010956961545276541/50000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506475447467269427/12500000000000000000 : ℝ) ≤ (625079319956187/625000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (12506475447467269427/12500000000000000000 : ℝ)^1024 ≤ (625079319956187/625000000000000 : ℝ)^4179 := by
      have hnat : (12506475447467269427 : ℕ)^1024*625000000000000^4179 ≤ 625079319956187^4179*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506475447467269427 12500000000000000000 625079319956187 625000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625079319956187/625000000000000 : ℝ)) (X := (12506475447467269427/12500000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (400326772945543031/400000000000000000 : ℝ) ≤ (5001000657929891/5000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (400326772945543031/400000000000000000 : ℝ)^1024 ≤ (5001000657929891/5000000000000000 : ℝ)^4179 := by
      have hnat : (400326772945543031 : ℕ)^1024*5000000000000000^4179 ≤ 5001000657929891^4179*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400326772945543031 400000000000000000 5001000657929891 5000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001000657929891/5000000000000000 : ℝ)) (X := (400326772945543031/400000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10956961545276541/100000000000000000000 : ℝ) ≤ ((20358255278973091423/20365000000000000000 : ℝ)+2*(73219656079/40730000000000 : ℝ)*(2141/20000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (20358255278973091423/20365000000000000000 : ℝ)+2*(73219656079/40730000000000 : ℝ)*(2141/20000 : ℝ)=(5000268461369101/5000000000000000 : ℝ) by norm_num, show 1+2*(10956961545276541/100000000000000000000 : ℝ)=(50010956961545276541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(326772945543031/800000000000000000 : ℝ)+(10956961545276541/100000000000000000000 : ℝ) ≤ ((20358255278973091423/20365000000000000000 : ℝ)+(73219656079/40730000000000 : ℝ)*((7389/50000 : ℝ)+(2141/20000 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (20358255278973091423/20365000000000000000 : ℝ)+(73219656079/40730000000000 : ℝ)*((7389/50000 : ℝ)+(2141/20000 : ℝ))=(625079319956187/625000000000000 : ℝ) by norm_num, show 1+(326772945543031/800000000000000000 : ℝ)+(10956961545276541/100000000000000000000 : ℝ)=(12506475447467269427/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(326772945543031/800000000000000000 : ℝ) ≤ ((20358255278973091423/20365000000000000000 : ℝ)+2*(73219656079/40730000000000 : ℝ)*(7389/50000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (20358255278973091423/20365000000000000000 : ℝ)+2*(73219656079/40730000000000 : ℝ)*(7389/50000 : ℝ)=(5001000657929891/5000000000000000 : ℝ) by norm_num, show 1+2*(326772945543031/800000000000000000 : ℝ)=(400326772945543031/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20358255278973091423/20365000000000000000 : ℝ)*(X 1 0+X 2 0)+(73219656079/40730000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (2141/20000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (20358255278973091423/20365000000000000000 : ℝ)) (alpha := (73219656079/40730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20358255278973091423/20365000000000000000 : ℝ)*(X 0 1+X 2 1)+(73219656079/40730000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (2141/20000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (20358255278973091423/20365000000000000000 : ℝ)) (alpha := (73219656079/40730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20358255278973091423/20365000000000000000 : ℝ)*(X 0 2+X 1 2)+(73219656079/40730000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (2141/20000 : ℝ)) (hi := (7389/50000 : ℝ)) (c := (20358255278973091423/20365000000000000000 : ℝ)) (alpha := (73219656079/40730000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-67335279/312500000 : ℝ)*X 0 0+(675095867/1250000000 : ℝ)*X 0 1+(1314607967/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673359583/5000000000 : ℝ)*X 1 0+(-2227044027/10000000000 : ℝ)*X 1 1+(2629216021/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346718713/10000000000 : ℝ)*X 2 0+(2629216157/5000000000 : ℝ)*X 2 1+(-2227044269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360875577/10000000000 : ℝ)*X 0 0+(52761481/125000000 : ℝ)*X 0 1+(2252711767/5000000000 : ℝ)*X 0 2+(4360875577/10000000000 : ℝ)*X 1 0+(52761481/125000000 : ℝ)*X 1 1+(2252711767/5000000000 : ℝ)*X 1 2+(4360875577/10000000000 : ℝ)*X 2 0+(52761481/125000000 : ℝ)*X 2 1+(2252711767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2154735613/10000000000 : ℝ)*X 0 0+(2629417261/5000000000 : ℝ)*X 0 1+(2700181393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310596459/10000000000 : ℝ)*X 1 0+(-2085113313/10000000000 : ℝ)*X 1 1+(1350090677/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310596303/10000000000 : ℝ)*X 2 0+(5400362641/10000000000 : ℝ)*X 2 1+(-417022723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360889409/10000000000 : ℝ)*X 0 0+(2252309343/5000000000 : ℝ)*X 0 1+(2110863259/5000000000 : ℝ)*X 0 2+(4360889409/10000000000 : ℝ)*X 1 0+(2252309343/5000000000 : ℝ)*X 1 1+(2110863259/5000000000 : ℝ)*X 1 2+(4360889409/10000000000 : ℝ)*X 2 0+(2252309343/5000000000 : ℝ)*X 2 1+(2110863259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (405399864494445323532357567/63640625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32642823/1562500000000 : ℝ)*(base19) + (765758593/50000000000000 : ℝ)*(base23) + (134316153/100000000000000 : ℝ)*(upper2) + (27170401/6250000000000 : ℝ)*(upper3) + (57096637/50000000000000 : ℝ)*(upper4) + (329397701793819/6250000000000 : ℝ)*(major0) + (329397701793819/6250000000000 : ℝ)*(major1) + (329397701793819/6250000000000 : ℝ)*(major2) + (7025748398559811/100000000000000 : ℝ)*(sp0) + (3512897043186247/50000000000000 : ℝ)*(sp1) + (351289732199799/5000000000000 : ℝ)*(sp2) + (1757450252879331/50000000000000 : ℝ)*(sp3) + (9555390671/20000000000000 : ℝ)*(sp4) + (29563792277/100000000000000 : ℝ)*(sp7) + (175746503477547/5000000000000 : ℝ)*(f.failure) + (3512898087756583/50000000000000 : ℝ)*(f.sum) + (846138373039/203650000000000000000000000 : ℝ)*base66 + (3004873800529939437/127281250000000000000000000000000 : ℝ)*base67 + (740099360991439437/127281250000000000000000000000000 : ℝ)*base69 + (1758405963090595687/127281250000000000000000000000000 : ℝ)*base71 + (511449467501/203650000000000000000000000 : ℝ)*base73 + (1283494994109876937/127281250000000000000000000000000 : ℝ)*base75 + (2232178120380345687/127281250000000000000000000000000 : ℝ)*base77 + (1631105973344876937/127281250000000000000000000000000 : ℝ)*base79 + (1519812212287/407300000000000000000000000 : ℝ)*base82 + (3440571/500000000000000000000 : ℝ)*base89 + (3440571/500000000000000000000 : ℝ)*base91 + (3440571/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (238243137325737656484331407/254562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104559717/10000000000000 : ℝ)*(base19) + (60604989/6250000000000 : ℝ)*(base23) + (61586827/50000000000000 : ℝ)*(upper2) + (52150501/50000000000000 : ℝ)*(upper5) + (2650161858158097/50000000000000 : ℝ)*(major0) + (2650161858158097/50000000000000 : ℝ)*(major1) + (2650161858158097/50000000000000 : ℝ)*(major2) + (1385673681/25000000000000 : ℝ)*(sp0) + (17772480789/50000000000000 : ℝ)*(sp1) + (10399803949/50000000000000 : ℝ)*(sp2) + (282629217214567/4000000000000 : ℝ)*(sp4) + (7065699382500151/100000000000000 : ℝ)*(sp5) + (883214275471397/12500000000000 : ℝ)*(sp6) + (441863928547133/12500000000000 : ℝ)*(sp7) + (441863928547133/12500000000000 : ℝ)*(f.failure) + (7065735973058899/100000000000000 : ℝ)*(f.sum) + (3198251538707/814600000000000000000000000 : ℝ)*base65 + (10395327084846702031/1018250000000000000000000000000000 : ℝ)*base67 + (5404958965404702031/1018250000000000000000000000000000 : ℝ)*base69 + (7096226089697952031/1018250000000000000000000000000000 : ℝ)*base71 + (9084516795097/4073000000000000000000000000 : ℝ)*base73 + (5087287799031797969/1018250000000000000000000000000000 : ℝ)*base76 + (12259783707401702031/1018250000000000000000000000000000 : ℝ)*base77 + (23313908849721202031/1018250000000000000000000000000000 : ℝ)*base79 + (800449678051/2036500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (882669/1250000000000000000000 : ℝ)*base89 + (882669/1250000000000000000000 : ℝ)*base91 + (882669/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1166_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7389/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2141/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1166_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1166_s5_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1077658361/5000000000 : ℝ)*x 0 + (1348572349/2500000000 : ℝ)*x 1 + (2632261661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077658361/5000000000 : ℝ)^8359 ≤ (13098662384471/100000000000000 : ℝ)^6311 := by
    have hnat : (1077658361 : ℕ)^8359*100000000000000^6311 ≤ 13098662384471^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077658361 5000000000 13098662384471 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348572349/2500000000 : ℝ)^8359 ≤ (22075649425193/50000000000000 : ℝ)^6311 := by
    have hnat : (1348572349 : ℕ)^8359*50000000000000^6311 ≤ 22075649425193^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348572349 2500000000 22075649425193 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632261661/5000000000 : ℝ)^8359 ≤ (42750038754631/100000000000000 : ℝ)^6311 := by
    have hnat : (2632261661 : ℕ)^8359*100000000000000^6311 ≤ 42750038754631^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632261661 5000000000 42750038754631 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1077658361/5000000000 : ℝ), (1348572349/2500000000 : ℝ), (2632261661/5000000000 : ℝ)] ![(13098662384471/100000000000000 : ℝ), (22075649425193/50000000000000 : ℝ), (42750038754631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1077658361/5000000000 : ℝ)|^8359 ≤ (13098662384471/100000000000000 : ℝ)^6311
        have hw : |(-1077658361/5000000000 : ℝ)|=(1077658361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348572349/2500000000 : ℝ)|^8359 ≤ (22075649425193/50000000000000 : ℝ)^6311
        have hw : |(1348572349/2500000000 : ℝ)|=(1348572349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632261661/5000000000 : ℝ)|^8359 ≤ (42750038754631/100000000000000 : ℝ)^6311
        have hw : |(2632261661/5000000000 : ℝ)|=(2632261661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672545071/5000000000 : ℝ)*x 0 + (-138822159/625000000 : ℝ)*x 1 + (5264523239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672545071/5000000000 : ℝ)^8359 ≤ (1744749021563/4000000000000 : ℝ)^6311 := by
    have hnat : (2672545071 : ℕ)^8359*4000000000000^6311 ≤ 1744749021563^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672545071 5000000000 1744749021563 4000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138822159/625000000 : ℝ)^8359 ≤ (13631236583561/100000000000000 : ℝ)^6311 := by
    have hnat : (138822159 : ℕ)^8359*100000000000000^6311 ≤ 13631236583561^6311*625000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138822159 625000000 13631236583561 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264523239/10000000000 : ℝ)^8359 ≤ (42750037861919/100000000000000 : ℝ)^6311 := by
    have hnat : (5264523239 : ℕ)^8359*100000000000000^6311 ≤ 42750037861919^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264523239 10000000000 42750037861919 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672545071/5000000000 : ℝ), (-138822159/625000000 : ℝ), (5264523239/10000000000 : ℝ)] ![(1744749021563/4000000000000 : ℝ), (13631236583561/100000000000000 : ℝ), (42750037861919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672545071/5000000000 : ℝ)|^8359 ≤ (1744749021563/4000000000000 : ℝ)^6311
        have hw : |(2672545071/5000000000 : ℝ)|=(2672545071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138822159/625000000 : ℝ)|^8359 ≤ (13631236583561/100000000000000 : ℝ)^6311
        have hw : |(-138822159/625000000 : ℝ)|=(138822159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264523239/10000000000 : ℝ)|^8359 ≤ (42750037861919/100000000000000 : ℝ)^6311
        have hw : |(5264523239/10000000000 : ℝ)|=(5264523239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345090021/10000000000 : ℝ)*x 0 + (658065403/1250000000 : ℝ)*x 1 + (-88846189/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345090021/10000000000 : ℝ)^8359 ≤ (2180936211561/5000000000000 : ℝ)^6311 := by
    have hnat : (5345090021 : ℕ)^8359*5000000000000^6311 ≤ 2180936211561^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345090021 10000000000 2180936211561 5000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658065403/1250000000 : ℝ)^8359 ≤ (8550007540117/20000000000000 : ℝ)^6311 := by
    have hnat : (658065403 : ℕ)^8359*20000000000000^6311 ≤ 8550007540117^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658065403 1250000000 8550007540117 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88846189/400000000 : ℝ)^8359 ≤ (13631238054827/100000000000000 : ℝ)^6311 := by
    have hnat : (88846189 : ℕ)^8359*100000000000000^6311 ≤ 13631238054827^6311*400000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88846189 400000000 13631238054827 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345090021/10000000000 : ℝ), (658065403/1250000000 : ℝ), (-88846189/400000000 : ℝ)] ![(2180936211561/5000000000000 : ℝ), (8550007540117/20000000000000 : ℝ), (13631238054827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345090021/10000000000 : ℝ)|^8359 ≤ (2180936211561/5000000000000 : ℝ)^6311
        have hw : |(5345090021/10000000000 : ℝ)|=(5345090021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658065403/1250000000 : ℝ)|^8359 ≤ (8550007540117/20000000000000 : ℝ)^6311
        have hw : |(658065403/1250000000 : ℝ)|=(658065403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-88846189/400000000 : ℝ)|^8359 ≤ (13631238054827/100000000000000 : ℝ)^6311
        have hw : |(-88846189/400000000 : ℝ)|=(88846189/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34072019/78125000 : ℝ)*x 0 + (1058358881/2500000000 : ℝ)*x 1 + (4492817793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34072019/78125000 : ℝ)^8359 ≤ (33316240282523/100000000000000 : ℝ)^6311 := by
    have hnat : (34072019 : ℕ)^8359*100000000000000^6311 ≤ 33316240282523^6311*78125000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34072019 78125000 33316240282523 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058358881/2500000000 : ℝ)^8359 ≤ (32029491971433/100000000000000 : ℝ)^6311 := by
    have hnat : (1058358881 : ℕ)^8359*100000000000000^6311 ≤ 32029491971433^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058358881 2500000000 32029491971433 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492817793/10000000000 : ℝ)^8359 ≤ (17327133865441/50000000000000 : ℝ)^6311 := by
    have hnat : (4492817793 : ℕ)^8359*50000000000000^6311 ≤ 17327133865441^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492817793 10000000000 17327133865441 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34072019/78125000 : ℝ), (1058358881/2500000000 : ℝ), (4492817793/10000000000 : ℝ)] ![(33316240282523/100000000000000 : ℝ), (32029491971433/100000000000000 : ℝ), (17327133865441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34072019/78125000 : ℝ)|^8359 ≤ (33316240282523/100000000000000 : ℝ)^6311
        have hw : |(34072019/78125000 : ℝ)|=(34072019/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058358881/2500000000 : ℝ)|^8359 ≤ (32029491971433/100000000000000 : ℝ)^6311
        have hw : |(1058358881/2500000000 : ℝ)|=(1058358881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492817793/10000000000 : ℝ)|^8359 ≤ (17327133865441/50000000000000 : ℝ)^6311
        have hw : |(4492817793/10000000000 : ℝ)|=(4492817793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-86212881/400000000 : ℝ)*x 0 + (5264857941/10000000000 : ℝ)*x 1 + (2696976733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86212881/400000000 : ℝ)^8359 ≤ (1309870507129/10000000000000 : ℝ)^6311 := by
    have hnat : (86212881 : ℕ)^8359*10000000000000^6311 ≤ 1309870507129^6311*400000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86212881 400000000 1309870507129 10000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264857941/10000000000 : ℝ)^8359 ≤ (42753637811257/100000000000000 : ℝ)^6311 := by
    have hnat : (5264857941 : ℕ)^8359*100000000000000^6311 ≤ 42753637811257^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264857941 10000000000 42753637811257 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696976733/5000000000 : ℝ)^8359 ≤ (22073828551619/50000000000000 : ℝ)^6311 := by
    have hnat : (2696976733 : ℕ)^8359*50000000000000^6311 ≤ 22073828551619^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696976733 5000000000 22073828551619 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86212881/400000000 : ℝ), (5264857941/10000000000 : ℝ), (2696976733/5000000000 : ℝ)] ![(1309870507129/10000000000000 : ℝ), (42753637811257/100000000000000 : ℝ), (22073828551619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86212881/400000000 : ℝ)|^8359 ≤ (1309870507129/10000000000000 : ℝ)^6311
        have hw : |(-86212881/400000000 : ℝ)|=(86212881/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264857941/10000000000 : ℝ)|^8359 ≤ (42753637811257/100000000000000 : ℝ)^6311
        have hw : |(5264857941/10000000000 : ℝ)|=(5264857941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696976733/5000000000 : ℝ)|^8359 ≤ (22073828551619/50000000000000 : ℝ)^6311
        have hw : |(2696976733/5000000000 : ℝ)|=(2696976733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656077859/5000000000 : ℝ)*x 0 + (-522931147/2500000000 : ℝ)*x 1 + (5393953359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656077859/5000000000 : ℝ)^8359 ≤ (675985986111/1562500000000 : ℝ)^6311 := by
    have hnat : (2656077859 : ℕ)^8359*1562500000000^6311 ≤ 675985986111^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656077859 5000000000 675985986111 1562500000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522931147/2500000000 : ℝ)^8359 ≤ (1573655115901/12500000000000 : ℝ)^6311 := by
    have hnat : (522931147 : ℕ)^8359*12500000000000^6311 ≤ 1573655115901^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522931147 2500000000 1573655115901 12500000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393953359/10000000000 : ℝ)^8359 ≤ (8829531188657/20000000000000 : ℝ)^6311 := by
    have hnat : (5393953359 : ℕ)^8359*20000000000000^6311 ≤ 8829531188657^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393953359 10000000000 8829531188657 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656077859/5000000000 : ℝ), (-522931147/2500000000 : ℝ), (5393953359/10000000000 : ℝ)] ![(675985986111/1562500000000 : ℝ), (1573655115901/12500000000000 : ℝ), (8829531188657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656077859/5000000000 : ℝ)|^8359 ≤ (675985986111/1562500000000 : ℝ)^6311
        have hw : |(2656077859/5000000000 : ℝ)|=(2656077859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522931147/2500000000 : ℝ)|^8359 ≤ (1573655115901/12500000000000 : ℝ)^6311
        have hw : |(-522931147/2500000000 : ℝ)|=(522931147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393953359/10000000000 : ℝ)|^8359 ≤ (8829531188657/20000000000000 : ℝ)^6311
        have hw : |(5393953359/10000000000 : ℝ)|=(5393953359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212486231/400000000 : ℝ)*x 0 + (674244171/1250000000 : ℝ)*x 1 + (-1045862249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212486231/400000000 : ℝ)^8359 ≤ (21631551862983/50000000000000 : ℝ)^6311 := by
    have hnat : (212486231 : ℕ)^8359*50000000000000^6311 ≤ 21631551862983^6311*400000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212486231 400000000 21631551862983 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674244171/1250000000 : ℝ)^8359 ≤ (44147656040851/100000000000000 : ℝ)^6311 := by
    have hnat : (674244171 : ℕ)^8359*100000000000000^6311 ≤ 44147656040851^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674244171 1250000000 44147656040851 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045862249/5000000000 : ℝ)^8359 ≤ (2517848041951/20000000000000 : ℝ)^6311 := by
    have hnat : (1045862249 : ℕ)^8359*20000000000000^6311 ≤ 2517848041951^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045862249 5000000000 2517848041951 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212486231/400000000 : ℝ), (674244171/1250000000 : ℝ), (-1045862249/5000000000 : ℝ)] ![(21631551862983/50000000000000 : ℝ), (44147656040851/100000000000000 : ℝ), (2517848041951/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212486231/400000000 : ℝ)|^8359 ≤ (21631551862983/50000000000000 : ℝ)^6311
        have hw : |(212486231/400000000 : ℝ)|=(212486231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674244171/1250000000 : ℝ)|^8359 ≤ (44147656040851/100000000000000 : ℝ)^6311
        have hw : |(674244171/1250000000 : ℝ)|=(674244171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1045862249/5000000000 : ℝ)|^8359 ≤ (2517848041951/20000000000000 : ℝ)^6311
        have hw : |(-1045862249/5000000000 : ℝ)|=(1045862249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_s5_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180614419/5000000000 : ℝ)*x 0 + (4492148777/10000000000 : ℝ)*x 1 + (846821407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180614419/5000000000 : ℝ)^8359 ≤ (8329086393201/25000000000000 : ℝ)^6311 := by
    have hnat : (2180614419 : ℕ)^8359*25000000000000^6311 ≤ 8329086393201^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180614419 5000000000 8329086393201 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492148777/10000000000 : ℝ)^8359 ≤ (34647433021131/100000000000000 : ℝ)^6311 := by
    have hnat : (4492148777 : ℕ)^8359*100000000000000^6311 ≤ 34647433021131^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492148777 10000000000 34647433021131 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846821407/2000000000 : ℝ)^8359 ≤ (32036221390181/100000000000000 : ℝ)^6311 := by
    have hnat : (846821407 : ℕ)^8359*100000000000000^6311 ≤ 32036221390181^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846821407 2000000000 32036221390181 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180614419/5000000000 : ℝ), (4492148777/10000000000 : ℝ), (846821407/2000000000 : ℝ)] ![(8329086393201/25000000000000 : ℝ), (34647433021131/100000000000000 : ℝ), (32036221390181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180614419/5000000000 : ℝ)|^8359 ≤ (8329086393201/25000000000000 : ℝ)^6311
        have hw : |(2180614419/5000000000 : ℝ)|=(2180614419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492148777/10000000000 : ℝ)|^8359 ≤ (34647433021131/100000000000000 : ℝ)^6311
        have hw : |(4492148777/10000000000 : ℝ)|=(4492148777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846821407/2000000000 : ℝ)|^8359 ≤ (32036221390181/100000000000000 : ℝ)^6311
        have hw : |(846821407/2000000000 : ℝ)|=(846821407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (227/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (561/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (561/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (561/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (561/5000 : ℝ) ^ (4179/1024 : ℝ) ≤ (414781060114841/3125000000000000000 : ℝ) := by
    have hpowers : (561/5000 : ℝ)^4179 ≤ (414781060114841/3125000000000000000 : ℝ)^1024 := by
      have hnat : (561 : ℕ)^4179*3125000000000000000^1024 ≤ 414781060114841^1024*5000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 5000 414781060114841 3125000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/5000 : ℝ)) (X := (414781060114841/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4179/1024 : ℝ) ≤ (17524717738846377/50000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4179 ≤ (17524717738846377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4179*50000000000000000000^1024 ≤ 17524717738846377^1024*50000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 17524717738846377 50000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (17524717738846377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562914781060114841/1562500000000000000 : ℝ) ≤ (10000650403638579/10000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (1562914781060114841/1562500000000000000 : ℝ)^1024 ≤ (10000650403638579/10000000000000000 : ℝ)^4179 := by
      have hnat : (1562914781060114841 : ℕ)^1024*10000000000000000^4179 ≤ 10000650403638579^4179*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562914781060114841 1562500000000000000 10000650403638579 10000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650403638579/10000000000000000 : ℝ)) (X := (1562914781060114841/1562500000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024161214700683833/50000000000000000000 : ℝ) ≤ (1250147981407859/1250000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (50024161214700683833/50000000000000000000 : ℝ)^1024 ≤ (1250147981407859/1250000000000000 : ℝ)^4179 := by
      have hnat : (50024161214700683833 : ℕ)^1024*1250000000000000^4179 ≤ 1250147981407859^4179*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024161214700683833 50000000000000000000 1250147981407859 1250000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250147981407859/1250000000000000 : ℝ)) (X := (50024161214700683833/50000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017524717738846377/25000000000000000000 : ℝ) ≤ (2000343459777433/2000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (25017524717738846377/25000000000000000000 : ℝ)^1024 ≤ (2000343459777433/2000000000000000 : ℝ)^4179 := by
      have hnat : (25017524717738846377 : ℕ)^1024*2000000000000000^4179 ≤ 2000343459777433^4179*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017524717738846377 25000000000000000000 2000343459777433 2000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000343459777433/2000000000000000 : ℝ)) (X := (25017524717738846377/25000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(414781060114841/3125000000000000000 : ℝ) ≤ ((1369544988721706463/1370000000000000000 : ℝ)+2*(533447624293/301400000000000 : ℝ)*(561/5000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (1369544988721706463/1370000000000000000 : ℝ)+2*(533447624293/301400000000000 : ℝ)*(561/5000 : ℝ)=(10000650403638579/10000000000000000 : ℝ) by norm_num, show 1+2*(414781060114841/3125000000000000000 : ℝ)=(1562914781060114841/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17524717738846377/50000000000000000000 : ℝ)+(414781060114841/3125000000000000000 : ℝ) ≤ ((1369544988721706463/1370000000000000000 : ℝ)+(533447624293/301400000000000 : ℝ)*((7117/50000 : ℝ)+(561/5000 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (1369544988721706463/1370000000000000000 : ℝ)+(533447624293/301400000000000 : ℝ)*((7117/50000 : ℝ)+(561/5000 : ℝ))=(1250147981407859/1250000000000000 : ℝ) by norm_num, show 1+(17524717738846377/50000000000000000000 : ℝ)+(414781060114841/3125000000000000000 : ℝ)=(50024161214700683833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17524717738846377/50000000000000000000 : ℝ) ≤ ((1369544988721706463/1370000000000000000 : ℝ)+2*(533447624293/301400000000000 : ℝ)*(7117/50000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (1369544988721706463/1370000000000000000 : ℝ)+2*(533447624293/301400000000000 : ℝ)*(7117/50000 : ℝ)=(2000343459777433/2000000000000000 : ℝ) by norm_num, show 1+2*(17524717738846377/50000000000000000000 : ℝ)=(25017524717738846377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1369544988721706463/1370000000000000000 : ℝ)*(X 1 0+X 2 0)+(533447624293/301400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1369544988721706463/1370000000000000000 : ℝ)) (alpha := (533447624293/301400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1369544988721706463/1370000000000000000 : ℝ)*(X 0 1+X 2 1)+(533447624293/301400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1369544988721706463/1370000000000000000 : ℝ)) (alpha := (533447624293/301400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1369544988721706463/1370000000000000000 : ℝ)*(X 0 2+X 1 2)+(533447624293/301400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (561/5000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (1369544988721706463/1370000000000000000 : ℝ)) (alpha := (533447624293/301400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1077658361/5000000000 : ℝ)*X 0 0+(1348572349/2500000000 : ℝ)*X 0 1+(2632261661/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672545071/5000000000 : ℝ)*X 1 0+(-138822159/625000000 : ℝ)*X 1 1+(5264523239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345090021/10000000000 : ℝ)*X 2 0+(658065403/1250000000 : ℝ)*X 2 1+(-88846189/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34072019/78125000 : ℝ)*X 0 0+(1058358881/2500000000 : ℝ)*X 0 1+(4492817793/10000000000 : ℝ)*X 0 2+(34072019/78125000 : ℝ)*X 1 0+(1058358881/2500000000 : ℝ)*X 1 1+(4492817793/10000000000 : ℝ)*X 1 2+(34072019/78125000 : ℝ)*X 2 0+(1058358881/2500000000 : ℝ)*X 2 1+(4492817793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-86212881/400000000 : ℝ)*X 0 0+(5264857941/10000000000 : ℝ)*X 0 1+(2696976733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656077859/5000000000 : ℝ)*X 1 0+(-522931147/2500000000 : ℝ)*X 1 1+(5393953359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212486231/400000000 : ℝ)*X 2 0+(674244171/1250000000 : ℝ)*X 2 1+(-1045862249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2180614419/5000000000 : ℝ)*X 0 0+(4492148777/10000000000 : ℝ)*X 0 1+(846821407/2000000000 : ℝ)*X 0 2+(2180614419/5000000000 : ℝ)*X 1 0+(4492148777/10000000000 : ℝ)*X 1 1+(846821407/2000000000 : ℝ)*X 1 2+(2180614419/5000000000 : ℝ)*X 2 0+(4492148777/10000000000 : ℝ)*X 2 1+(846821407/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (537940901803013684115064887/68500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25766441/4000000000000 : ℝ)*(base19) + (776223857/100000000000000 : ℝ)*(base23) + (8336639/100000000000000 : ℝ)*(lower2) + (90423471/100000000000000 : ℝ)*(upper3) + (172170529/100000000000000 : ℝ)*(lower4) + (5780770924600483/100000000000000 : ℝ)*(major0) + (5780770924600483/100000000000000 : ℝ)*(major1) + (5780770924600483/100000000000000 : ℝ)*(major2) + (3853098448083731/50000000000000 : ℝ)*(sp0) + (3853103945974947/50000000000000 : ℝ)*(sp1) + (7706207759887063/100000000000000 : ℝ)*(sp2) + (963830925604887/25000000000000 : ℝ)*(sp3) + (11639943457/100000000000000 : ℝ)*(sp4) + (9348898757/100000000000000 : ℝ)*(sp7) + (1927666525659153/50000000000000 : ℝ)*(f.failure) + (192655213402773/2500000000000 : ℝ)*(f.sum) + (55220916020609/15070000000000000000000000000 : ℝ)*base65 + (8835604184380187919/1507000000000000000000000000000000 : ℝ)*base67 + (20814809876304812081/1507000000000000000000000000000000 : ℝ)*base70 + (16291728226340187919/1507000000000000000000000000000000 : ℝ)*base71 + (30907703008169/15070000000000000000000000000 : ℝ)*base73 + (2641694847884812081/1507000000000000000000000000000000 : ℝ)*base76 + (21309358509784812081/1507000000000000000000000000000000 : ℝ)*base78 + (41040634632980812081/1507000000000000000000000000000000 : ℝ)*base80 + (40552358953361/15070000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (21342529/5000000000000000000000 : ℝ)*base89 + (21342529/5000000000000000000000 : ℝ)*base91 + (21342529/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4413699180216108826699317027/376750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1276667189/100000000000000 : ℝ)*(base19) + (42160867/2500000000000 : ℝ)*(base23) + (142289343/100000000000000 : ℝ)*(upper3) + (133763337/100000000000000 : ℝ)*(lower4) + (42460613/25000000000000 : ℝ)*(upper5) + (2905385564563613/50000000000000 : ℝ)*(major0) + (2905385564563613/50000000000000 : ℝ)*(major1) + (2905385564563613/50000000000000 : ℝ)*(major2) + (28035604447/100000000000000 : ℝ)*(sp1) + (10026937377/25000000000000 : ℝ)*(sp2) + (1549240193890891/20000000000000 : ℝ)*(sp4) + (7746171657182819/100000000000000 : ℝ)*(sp5) + (3873079587635133/50000000000000 : ℝ)*(sp6) + (775068179658707/20000000000000 : ℝ)*(sp7) + (775068179658707/20000000000000 : ℝ)*(f.failure) + (1549240193890891/20000000000000 : ℝ)*(f.sum) + (395803076171/1883750000000000000000000000 : ℝ)*base65 + (4545898793400510991/753500000000000000000000000000000 : ℝ)*base68 + (6050243387818010991/753500000000000000000000000000000 : ℝ)*base70 + (8588661863113489009/753500000000000000000000000000000 : ℝ)*base71 + (5911095530079/1883750000000000000000000000 : ℝ)*base74 + (33167948727202010991/753500000000000000000000000000000 : ℝ)*base76 + (2332445323056489009/753500000000000000000000000000000 : ℝ)*base77 + (776102520988010991/753500000000000000000000000000000 : ℝ)*base80 + (19287759810193/3767500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (875549/2000000000000000000000 : ℝ)*base90 + (875549/2000000000000000000000 : ℝ)*base92 + (875549/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1166_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (561/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1166_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1166_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1166_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1166_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1166_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1027/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4589/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (227/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1166_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
