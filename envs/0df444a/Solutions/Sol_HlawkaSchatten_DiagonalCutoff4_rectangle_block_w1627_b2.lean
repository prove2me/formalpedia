-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:12.363668+00:00
-- url     : https://prove2.me/submissions/7cd506c0-406f-4949-8a30-5fa340e3dc3b

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
theorem support_rectangle_w1627_box_0 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87242839/625000000 : ℝ)*x 0 + (1353446417/2500000000 : ℝ)*x 1 + (5413784403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87242839/625000000 : ℝ)^4827 ≤ (205367199927/2500000000000 : ℝ)^3803 := by
    have hnat : (87242839 : ℕ)^4827*2500000000000^3803 ≤ 205367199927^3803*625000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87242839 625000000 205367199927 2500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353446417/2500000000 : ℝ)^4827 ≤ (22946331399691/50000000000000 : ℝ)^3803 := by
    have hnat : (1353446417 : ℕ)^4827*50000000000000^3803 ≤ 22946331399691^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353446417 2500000000 22946331399691 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413784403/10000000000 : ℝ)^4827 ≤ (45892649188581/100000000000000 : ℝ)^3803 := by
    have hnat : (5413784403 : ℕ)^4827*100000000000000^3803 ≤ 45892649188581^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413784403 10000000000 45892649188581 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87242839/625000000 : ℝ), (1353446417/2500000000 : ℝ), (5413784403/10000000000 : ℝ)] ![(205367199927/2500000000000 : ℝ), (22946331399691/50000000000000 : ℝ), (45892649188581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87242839/625000000 : ℝ)|^4827 ≤ (205367199927/2500000000000 : ℝ)^3803
        have hw : |(-87242839/625000000 : ℝ)|=(87242839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353446417/2500000000 : ℝ)|^4827 ≤ (22946331399691/50000000000000 : ℝ)^3803
        have hw : |(1353446417/2500000000 : ℝ)|=(1353446417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413784403/10000000000 : ℝ)|^4827 ≤ (45892649188581/100000000000000 : ℝ)^3803
        have hw : |(5413784403/10000000000 : ℝ)|=(5413784403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_1 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251254759/10000000000 : ℝ)*x 0 + (-101513181/625000000 : ℝ)*x 1 + (5413784107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251254759/10000000000 : ℝ)^4827 ≤ (44151027675571/100000000000000 : ℝ)^3803 := by
    have hnat : (5251254759 : ℕ)^4827*100000000000000^3803 ≤ 44151027675571^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251254759 10000000000 44151027675571 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (101513181/625000000 : ℝ)^4827 ≤ (4978163152981/50000000000000 : ℝ)^3803 := by
    have hnat : (101513181 : ℕ)^4827*50000000000000^3803 ≤ 4978163152981^3803*625000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101513181 625000000 4978163152981 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413784107/10000000000 : ℝ)^4827 ≤ (45892646003761/100000000000000 : ℝ)^3803 := by
    have hnat : (5413784107 : ℕ)^4827*100000000000000^3803 ≤ 45892646003761^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413784107 10000000000 45892646003761 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251254759/10000000000 : ℝ), (-101513181/625000000 : ℝ), (5413784107/10000000000 : ℝ)] ![(44151027675571/100000000000000 : ℝ), (4978163152981/50000000000000 : ℝ), (45892646003761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251254759/10000000000 : ℝ)|^4827 ≤ (44151027675571/100000000000000 : ℝ)^3803
        have hw : |(5251254759/10000000000 : ℝ)|=(5251254759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-101513181/625000000 : ℝ)|^4827 ≤ (4978163152981/50000000000000 : ℝ)^3803
        have hw : |(-101513181/625000000 : ℝ)|=(101513181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413784107/10000000000 : ℝ)|^4827 ≤ (45892646003761/100000000000000 : ℝ)^3803
        have hw : |(5413784107/10000000000 : ℝ)|=(5413784107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_2 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625626837/5000000000 : ℝ)*x 0 + (1082757043/2000000000 : ℝ)*x 1 + (-406052713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625626837/5000000000 : ℝ)^4827 ≤ (11037754024227/25000000000000 : ℝ)^3803 := by
    have hnat : (2625626837 : ℕ)^4827*25000000000000^3803 ≤ 11037754024227^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625626837 5000000000 11037754024227 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082757043/2000000000 : ℝ)^4827 ≤ (11473164481329/25000000000000 : ℝ)^3803 := by
    have hnat : (1082757043 : ℕ)^4827*25000000000000^3803 ≤ 11473164481329^3803*2000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082757043 2000000000 11473164481329 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406052713/2500000000 : ℝ)^4827 ≤ (497816298181/5000000000000 : ℝ)^3803 := by
    have hnat : (406052713 : ℕ)^4827*5000000000000^3803 ≤ 497816298181^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406052713 2500000000 497816298181 5000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625626837/5000000000 : ℝ), (1082757043/2000000000 : ℝ), (-406052713/2500000000 : ℝ)] ![(11037754024227/25000000000000 : ℝ), (11473164481329/25000000000000 : ℝ), (497816298181/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625626837/5000000000 : ℝ)|^4827 ≤ (11037754024227/25000000000000 : ℝ)^3803
        have hw : |(2625626837/5000000000 : ℝ)|=(2625626837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082757043/2000000000 : ℝ)|^4827 ≤ (11473164481329/25000000000000 : ℝ)^3803
        have hw : |(1082757043/2000000000 : ℝ)|=(1082757043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406052713/2500000000 : ℝ)|^4827 ≤ (497816298181/5000000000000 : ℝ)^3803
        have hw : |(-406052713/2500000000 : ℝ)|=(406052713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_3 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4477207643/10000000000 : ℝ)*x 0 + (4071941799/10000000000 : ℝ)*x 1 + (2035970499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4477207643/10000000000 : ℝ)^4827 ≤ (18030470598633/50000000000000 : ℝ)^3803 := by
    have hnat : (4477207643 : ℕ)^4827*50000000000000^3803 ≤ 18030470598633^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477207643 10000000000 18030470598633 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4071941799/10000000000 : ℝ)^4827 ≤ (7992383345889/25000000000000 : ℝ)^3803 := by
    have hnat : (4071941799 : ℕ)^4827*25000000000000^3803 ≤ 7992383345889^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4071941799 10000000000 7992383345889 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035970499/5000000000 : ℝ)^4827 ≤ (31969525401437/100000000000000 : ℝ)^3803 := by
    have hnat : (2035970499 : ℕ)^4827*100000000000000^3803 ≤ 31969525401437^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035970499 5000000000 31969525401437 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4477207643/10000000000 : ℝ), (4071941799/10000000000 : ℝ), (2035970499/5000000000 : ℝ)] ![(18030470598633/50000000000000 : ℝ), (7992383345889/25000000000000 : ℝ), (31969525401437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4477207643/10000000000 : ℝ)|^4827 ≤ (18030470598633/50000000000000 : ℝ)^3803
        have hw : |(4477207643/10000000000 : ℝ)|=(4477207643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4071941799/10000000000 : ℝ)|^4827 ≤ (7992383345889/25000000000000 : ℝ)^3803
        have hw : |(4071941799/10000000000 : ℝ)|=(4071941799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2035970499/5000000000 : ℝ)|^4827 ≤ (31969525401437/100000000000000 : ℝ)^3803
        have hw : |(2035970499/5000000000 : ℝ)|=(2035970499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_4 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1939645233/10000000000 : ℝ)*x 0 + (5214957287/10000000000 : ℝ)*x 1 + (1303739239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1939645233/10000000000 : ℝ)^4827 ≤ (2494385746069/20000000000000 : ℝ)^3803 := by
    have hnat : (1939645233 : ℕ)^4827*20000000000000^3803 ≤ 2494385746069^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939645233 10000000000 2494385746069 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214957287/10000000000 : ℝ)^4827 ≤ (21882018696027/50000000000000 : ℝ)^3803 := by
    have hnat : (5214957287 : ℕ)^4827*50000000000000^3803 ≤ 21882018696027^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214957287 10000000000 21882018696027 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303739239/2500000000 : ℝ)^4827 ≤ (2735252116647/6250000000000 : ℝ)^3803 := by
    have hnat : (1303739239 : ℕ)^4827*6250000000000^3803 ≤ 2735252116647^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303739239 2500000000 2735252116647 6250000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1939645233/10000000000 : ℝ), (5214957287/10000000000 : ℝ), (1303739239/2500000000 : ℝ)] ![(2494385746069/20000000000000 : ℝ), (21882018696027/50000000000000 : ℝ), (2735252116647/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1939645233/10000000000 : ℝ)|^4827 ≤ (2494385746069/20000000000000 : ℝ)^3803
        have hw : |(-1939645233/10000000000 : ℝ)|=(1939645233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214957287/10000000000 : ℝ)|^4827 ≤ (21882018696027/50000000000000 : ℝ)^3803
        have hw : |(5214957287/10000000000 : ℝ)|=(5214957287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303739239/2500000000 : ℝ)|^4827 ≤ (2735252116647/6250000000000 : ℝ)^3803
        have hw : |(1303739239/2500000000 : ℝ)|=(1303739239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_5 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673519273/1250000000 : ℝ)*x 0 + (-1708785039/10000000000 : ℝ)*x 1 + (325934801/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673519273/1250000000 : ℝ)^4827 ≤ (22808528074243/50000000000000 : ℝ)^3803 := by
    have hnat : (673519273 : ℕ)^4827*50000000000000^3803 ≤ 22808528074243^3803*1250000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673519273 1250000000 22808528074243 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708785039/10000000000 : ℝ)^4827 ≤ (2654727865193/25000000000000 : ℝ)^3803 := by
    have hnat : (1708785039 : ℕ)^4827*25000000000000^3803 ≤ 2654727865193^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708785039 10000000000 2654727865193 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325934801/625000000 : ℝ)^4827 ≤ (21882016187559/50000000000000 : ℝ)^3803 := by
    have hnat : (325934801 : ℕ)^4827*50000000000000^3803 ≤ 21882016187559^3803*625000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325934801 625000000 21882016187559 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673519273/1250000000 : ℝ), (-1708785039/10000000000 : ℝ), (325934801/625000000 : ℝ)] ![(22808528074243/50000000000000 : ℝ), (2654727865193/25000000000000 : ℝ), (21882016187559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673519273/1250000000 : ℝ)|^4827 ≤ (22808528074243/50000000000000 : ℝ)^3803
        have hw : |(673519273/1250000000 : ℝ)|=(673519273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1708785039/10000000000 : ℝ)|^4827 ≤ (2654727865193/25000000000000 : ℝ)^3803
        have hw : |(-1708785039/10000000000 : ℝ)|=(1708785039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325934801/625000000 : ℝ)|^4827 ≤ (21882016187559/50000000000000 : ℝ)^3803
        have hw : |(325934801/625000000 : ℝ)|=(325934801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_6 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388153961/10000000000 : ℝ)*x 0 + (5214957113/10000000000 : ℝ)*x 1 + (-854392471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388153961/10000000000 : ℝ)^4827 ≤ (2851065859511/6250000000000 : ℝ)^3803 := by
    have hnat : (5388153961 : ℕ)^4827*6250000000000^3803 ≤ 2851065859511^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388153961 10000000000 2851065859511 6250000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214957113/10000000000 : ℝ)^4827 ≤ (43764035538663/100000000000000 : ℝ)^3803 := by
    have hnat : (5214957113 : ℕ)^4827*100000000000000^3803 ≤ 43764035538663^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214957113 10000000000 43764035538663 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (854392471/5000000000 : ℝ)^4827 ≤ (10618910695677/100000000000000 : ℝ)^3803 := by
    have hnat : (854392471 : ℕ)^4827*100000000000000^3803 ≤ 10618910695677^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854392471 5000000000 10618910695677 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388153961/10000000000 : ℝ), (5214957113/10000000000 : ℝ), (-854392471/5000000000 : ℝ)] ![(2851065859511/6250000000000 : ℝ), (43764035538663/100000000000000 : ℝ), (10618910695677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388153961/10000000000 : ℝ)|^4827 ≤ (2851065859511/6250000000000 : ℝ)^3803
        have hw : |(5388153961/10000000000 : ℝ)|=(5388153961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214957113/10000000000 : ℝ)|^4827 ≤ (43764035538663/100000000000000 : ℝ)^3803
        have hw : |(5214957113/10000000000 : ℝ)|=(5214957113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-854392471/5000000000 : ℝ)|^4827 ≤ (10618910695677/100000000000000 : ℝ)^3803
        have hw : |(-854392471/5000000000 : ℝ)|=(854392471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_7 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3914149321/10000000000 : ℝ)*x 0 + (1088283847/2500000000 : ℝ)*x 1 + (1088283867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3914149321/10000000000 : ℝ)^4827 ≤ (30405383187511/100000000000000 : ℝ)^3803 := by
    have hnat : (3914149321 : ℕ)^4827*100000000000000^3803 ≤ 30405383187511^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3914149321 10000000000 30405383187511 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088283847/2500000000 : ℝ)^4827 ≤ (34797307995639/100000000000000 : ℝ)^3803 := by
    have hnat : (1088283847 : ℕ)^4827*100000000000000^3803 ≤ 34797307995639^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088283847 2500000000 34797307995639 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088283867/2500000000 : ℝ)^4827 ≤ (17398654403659/50000000000000 : ℝ)^3803 := by
    have hnat : (1088283867 : ℕ)^4827*50000000000000^3803 ≤ 17398654403659^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088283867 2500000000 17398654403659 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3914149321/10000000000 : ℝ), (1088283847/2500000000 : ℝ), (1088283867/2500000000 : ℝ)] ![(30405383187511/100000000000000 : ℝ), (34797307995639/100000000000000 : ℝ), (17398654403659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3914149321/10000000000 : ℝ)|^4827 ≤ (30405383187511/100000000000000 : ℝ)^3803
        have hw : |(3914149321/10000000000 : ℝ)|=(3914149321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088283847/2500000000 : ℝ)|^4827 ≤ (34797307995639/100000000000000 : ℝ)^3803
        have hw : |(1088283847/2500000000 : ℝ)|=(1088283847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088283867/2500000000 : ℝ)|^4827 ≤ (17398654403659/50000000000000 : ℝ)^3803
        have hw : |(1088283867/2500000000 : ℝ)|=(1088283867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_8 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455965319/2500000000 : ℝ)*x 0 + (202900757/400000000 : ℝ)*x 1 + (5443524023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455965319/2500000000 : ℝ)^4827 ≤ (576734112369/5000000000000 : ℝ)^3803 := by
    have hnat : (455965319 : ℕ)^4827*5000000000000^3803 ≤ 576734112369^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455965319 2500000000 576734112369 5000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202900757/400000000 : ℝ)^4827 ≤ (42252447997877/100000000000000 : ℝ)^3803 := by
    have hnat : (202900757 : ℕ)^4827*100000000000000^3803 ≤ 42252447997877^3803*400000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202900757 400000000 42252447997877 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443524023/10000000000 : ℝ)^4827 ≤ (23106434870863/50000000000000 : ℝ)^3803 := by
    have hnat : (5443524023 : ℕ)^4827*50000000000000^3803 ≤ 23106434870863^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443524023 10000000000 23106434870863 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455965319/2500000000 : ℝ), (202900757/400000000 : ℝ), (5443524023/10000000000 : ℝ)] ![(576734112369/5000000000000 : ℝ), (42252447997877/100000000000000 : ℝ), (23106434870863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455965319/2500000000 : ℝ)|^4827 ≤ (576734112369/5000000000000 : ℝ)^3803
        have hw : |(-455965319/2500000000 : ℝ)|=(455965319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(202900757/400000000 : ℝ)|^4827 ≤ (42252447997877/100000000000000 : ℝ)^3803
        have hw : |(202900757/400000000 : ℝ)|=(202900757/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443524023/10000000000 : ℝ)|^4827 ≤ (23106434870863/50000000000000 : ℝ)^3803
        have hw : |(5443524023/10000000000 : ℝ)|=(5443524023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_9 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615387891/5000000000 : ℝ)*x 0 + (-20138917/125000000 : ℝ)*x 1 + (5443523931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615387891/5000000000 : ℝ)^4827 ≤ (17573039799/40000000000 : ℝ)^3803 := by
    have hnat : (2615387891 : ℕ)^4827*40000000000^3803 ≤ 17573039799^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615387891 5000000000 17573039799 40000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20138917/125000000 : ℝ)^4827 ≤ (9854531739547/100000000000000 : ℝ)^3803 := by
    have hnat : (20138917 : ℕ)^4827*100000000000000^3803 ≤ 9854531739547^3803*125000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20138917 125000000 9854531739547 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443523931/10000000000 : ℝ)^4827 ≤ (11553217187597/25000000000000 : ℝ)^3803 := by
    have hnat : (5443523931 : ℕ)^4827*25000000000000^3803 ≤ 11553217187597^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443523931 10000000000 11553217187597 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615387891/5000000000 : ℝ), (-20138917/125000000 : ℝ), (5443523931/10000000000 : ℝ)] ![(17573039799/40000000000 : ℝ), (9854531739547/100000000000000 : ℝ), (11553217187597/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615387891/5000000000 : ℝ)|^4827 ≤ (17573039799/40000000000 : ℝ)^3803
        have hw : |(2615387891/5000000000 : ℝ)|=(2615387891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20138917/125000000 : ℝ)|^4827 ≤ (9854531739547/100000000000000 : ℝ)^3803
        have hw : |(-20138917/125000000 : ℝ)|=(20138917/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443523931/10000000000 : ℝ)|^4827 ≤ (11553217187597/25000000000000 : ℝ)^3803
        have hw : |(5443523931/10000000000 : ℝ)|=(5443523931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_10 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (326923477/625000000 : ℝ)*x 0 + (5443523931/10000000000 : ℝ)*x 1 + (-805556783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326923477/625000000 : ℝ)^4827 ≤ (21966298949223/50000000000000 : ℝ)^3803 := by
    have hnat : (326923477 : ℕ)^4827*50000000000000^3803 ≤ 21966298949223^3803*625000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326923477 625000000 21966298949223 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443523931/10000000000 : ℝ)^4827 ≤ (11553217187597/25000000000000 : ℝ)^3803 := by
    have hnat : (5443523931 : ℕ)^4827*25000000000000^3803 ≤ 11553217187597^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443523931 10000000000 11553217187597 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805556783/5000000000 : ℝ)^4827 ≤ (246363333471/2500000000000 : ℝ)^3803 := by
    have hnat : (805556783 : ℕ)^4827*2500000000000^3803 ≤ 246363333471^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805556783 5000000000 246363333471 2500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326923477/625000000 : ℝ), (5443523931/10000000000 : ℝ), (-805556783/5000000000 : ℝ)] ![(21966298949223/50000000000000 : ℝ), (11553217187597/25000000000000 : ℝ), (246363333471/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326923477/625000000 : ℝ)|^4827 ≤ (21966298949223/50000000000000 : ℝ)^3803
        have hw : |(326923477/625000000 : ℝ)|=(326923477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443523931/10000000000 : ℝ)|^4827 ≤ (11553217187597/25000000000000 : ℝ)^3803
        have hw : |(5443523931/10000000000 : ℝ)|=(5443523931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-805556783/5000000000 : ℝ)|^4827 ≤ (246363333471/2500000000000 : ℝ)^3803
        have hw : |(-805556783/5000000000 : ℝ)|=(805556783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_11 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4559036387/10000000000 : ℝ)*x 0 + (4029806679/10000000000 : ℝ)*x 1 + (402980659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4559036387/10000000000 : ℝ)^4827 ≤ (4612441304939/12500000000000 : ℝ)^3803 := by
    have hnat : (4559036387 : ℕ)^4827*12500000000000^3803 ≤ 4612441304939^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559036387 10000000000 4612441304939 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029806679/10000000000 : ℝ)^4827 ≤ (31550235213423/100000000000000 : ℝ)^3803 := by
    have hnat : (4029806679 : ℕ)^4827*100000000000000^3803 ≤ 31550235213423^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029806679 10000000000 31550235213423 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402980659/1000000000 : ℝ)^4827 ≤ (31550234329001/100000000000000 : ℝ)^3803 := by
    have hnat : (402980659 : ℕ)^4827*100000000000000^3803 ≤ 31550234329001^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402980659 1000000000 31550234329001 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4559036387/10000000000 : ℝ), (4029806679/10000000000 : ℝ), (402980659/1000000000 : ℝ)] ![(4612441304939/12500000000000 : ℝ), (31550235213423/100000000000000 : ℝ), (31550234329001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4559036387/10000000000 : ℝ)|^4827 ≤ (4612441304939/12500000000000 : ℝ)^3803
        have hw : |(4559036387/10000000000 : ℝ)|=(4559036387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029806679/10000000000 : ℝ)|^4827 ≤ (31550235213423/100000000000000 : ℝ)^3803
        have hw : |(4029806679/10000000000 : ℝ)|=(4029806679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(402980659/1000000000 : ℝ)|^4827 ≤ (31550234329001/100000000000000 : ℝ)^3803
        have hw : |(402980659/1000000000 : ℝ)|=(402980659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_12 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-23596913/156250000 : ℝ)*x 0 + (173455883/312500000 : ℝ)*x 1 + (1298774593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23596913/156250000 : ℝ)^4827 ≤ (9077813643087/100000000000000 : ℝ)^3803 := by
    have hnat : (23596913 : ℕ)^4827*100000000000000^3803 ≤ 9077813643087^3803*156250000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23596913 156250000 9077813643087 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173455883/312500000 : ℝ)^4827 ≤ (9473914192887/20000000000000 : ℝ)^3803 := by
    have hnat : (173455883 : ℕ)^4827*20000000000000^3803 ≤ 9473914192887^3803*312500000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173455883 312500000 9473914192887 20000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298774593/2500000000 : ℝ)^4827 ≤ (21776307691389/50000000000000 : ℝ)^3803 := by
    have hnat : (1298774593 : ℕ)^4827*50000000000000^3803 ≤ 21776307691389^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298774593 2500000000 21776307691389 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23596913/156250000 : ℝ), (173455883/312500000 : ℝ), (1298774593/2500000000 : ℝ)] ![(9077813643087/100000000000000 : ℝ), (9473914192887/20000000000000 : ℝ), (21776307691389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23596913/156250000 : ℝ)|^4827 ≤ (9077813643087/100000000000000 : ℝ)^3803
        have hw : |(-23596913/156250000 : ℝ)|=(23596913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(173455883/312500000 : ℝ)|^4827 ≤ (9473914192887/20000000000000 : ℝ)^3803
        have hw : |(173455883/312500000 : ℝ)|=(173455883/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298774593/2500000000 : ℝ)|^4827 ≤ (21776307691389/50000000000000 : ℝ)^3803
        have hw : |(1298774593/2500000000 : ℝ)|=(1298774593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_13 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401835177/10000000000 : ℝ)*x 0 + (-1716938469/10000000000 : ℝ)*x 1 + (519509853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401835177/10000000000 : ℝ)^4827 ≤ (45764119404141/100000000000000 : ℝ)^3803 := by
    have hnat : (5401835177 : ℕ)^4827*100000000000000^3803 ≤ 45764119404141^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401835177 10000000000 45764119404141 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716938469/10000000000 : ℝ)^4827 ≤ (10683263521567/100000000000000 : ℝ)^3803 := by
    have hnat : (1716938469 : ℕ)^4827*100000000000000^3803 ≤ 10683263521567^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716938469 10000000000 10683263521567 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519509853/1000000000 : ℝ)^4827 ≤ (21776308532007/50000000000000 : ℝ)^3803 := by
    have hnat : (519509853 : ℕ)^4827*50000000000000^3803 ≤ 21776308532007^3803*1000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519509853 1000000000 21776308532007 50000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401835177/10000000000 : ℝ), (-1716938469/10000000000 : ℝ), (519509853/1000000000 : ℝ)] ![(45764119404141/100000000000000 : ℝ), (10683263521567/100000000000000 : ℝ), (21776308532007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401835177/10000000000 : ℝ)|^4827 ≤ (45764119404141/100000000000000 : ℝ)^3803
        have hw : |(5401835177/10000000000 : ℝ)|=(5401835177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716938469/10000000000 : ℝ)|^4827 ≤ (10683263521567/100000000000000 : ℝ)^3803
        have hw : |(-1716938469/10000000000 : ℝ)|=(1716938469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519509853/1000000000 : ℝ)|^4827 ≤ (21776308532007/50000000000000 : ℝ)^3803
        have hw : |(519509853/1000000000 : ℝ)|=(519509853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_14 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350458787/2500000000 : ℝ)*x 0 + (5195098699/10000000000 : ℝ)*x 1 + (-42923457/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350458787/2500000000 : ℝ)^4827 ≤ (45764119092301/100000000000000 : ℝ)^3803 := by
    have hnat : (1350458787 : ℕ)^4827*100000000000000^3803 ≤ 45764119092301^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350458787 2500000000 45764119092301 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195098699/10000000000 : ℝ)^4827 ≤ (43552618862297/100000000000000 : ℝ)^3803 := by
    have hnat : (5195098699 : ℕ)^4827*100000000000000^3803 ≤ 43552618862297^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195098699 10000000000 43552618862297 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42923457/250000000 : ℝ)^4827 ≤ (1335407753613/12500000000000 : ℝ)^3803 := by
    have hnat : (42923457 : ℕ)^4827*12500000000000^3803 ≤ 1335407753613^3803*250000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42923457 250000000 1335407753613 12500000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350458787/2500000000 : ℝ), (5195098699/10000000000 : ℝ), (-42923457/250000000 : ℝ)] ![(45764119092301/100000000000000 : ℝ), (43552618862297/100000000000000 : ℝ), (1335407753613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350458787/2500000000 : ℝ)|^4827 ≤ (45764119092301/100000000000000 : ℝ)^3803
        have hw : |(1350458787/2500000000 : ℝ)|=(1350458787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195098699/10000000000 : ℝ)|^4827 ≤ (43552618862297/100000000000000 : ℝ)^3803
        have hw : |(5195098699/10000000000 : ℝ)|=(5195098699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42923457/250000000 : ℝ)|^4827 ≤ (1335407753613/12500000000000 : ℝ)^3803
        have hw : |(-42923457/250000000 : ℝ)|=(42923457/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1627_box_15 (p : ℝ) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1928142841/5000000000 : ℝ)*x 0 + (1095292573/2500000000 : ℝ)*x 1 + (4381170647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928142841/5000000000 : ℝ)^4827 ≤ (29836004189073/100000000000000 : ℝ)^3803 := by
    have hnat : (1928142841 : ℕ)^4827*100000000000000^3803 ≤ 29836004189073^3803*5000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928142841 5000000000 29836004189073 100000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095292573/2500000000 : ℝ)^4827 ≤ (8770499024833/25000000000000 : ℝ)^3803 := by
    have hnat : (1095292573 : ℕ)^4827*25000000000000^3803 ≤ 8770499024833^3803*2500000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095292573 2500000000 8770499024833 25000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4381170647/10000000000 : ℝ)^4827 ≤ (3508199970739/10000000000000 : ℝ)^3803 := by
    have hnat : (4381170647 : ℕ)^4827*10000000000000^3803 ≤ 3508199970739^3803*10000000000^4827 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381170647 10000000000 3508199970739 10000000000000 4827 3803 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4827/1024 : ℝ)) 4827 3803 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1928142841/5000000000 : ℝ), (1095292573/2500000000 : ℝ), (4381170647/10000000000 : ℝ)] ![(29836004189073/100000000000000 : ℝ), (8770499024833/25000000000000 : ℝ), (3508199970739/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1928142841/5000000000 : ℝ)|^4827 ≤ (29836004189073/100000000000000 : ℝ)^3803
        have hw : |(1928142841/5000000000 : ℝ)|=(1928142841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095292573/2500000000 : ℝ)|^4827 ≤ (8770499024833/25000000000000 : ℝ)^3803
        have hw : |(1095292573/2500000000 : ℝ)|=(1095292573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4381170647/10000000000 : ℝ)|^4827 ≤ (3508199970739/10000000000000 : ℝ)^3803
        have hw : |(4381170647/10000000000 : ℝ)|=(4381170647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1627_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64977/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29189/50000 : ℝ) ∧ (80767/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87997/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5271/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16311/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5271/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5271/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16311/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5271/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5271/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16311/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5271/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5271/50000 : ℝ) ^ (4823/1024 : ℝ) ≤ (500075466413477/20000000000000000000 : ℝ) := by
    have hpowers : (5271/50000 : ℝ)^4823 ≤ (500075466413477/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5271 : ℕ)^4823*20000000000000000000^1024 ≤ 500075466413477^1024*50000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5271 50000 500075466413477 20000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5271/50000 : ℝ)) (X := (500075466413477/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16311/100000 : ℝ) ^ (4823/1024 : ℝ) ≤ (9767520580716191/50000000000000000000 : ℝ) := by
    have hpowers : (16311/100000 : ℝ)^4823 ≤ (9767520580716191/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16311 : ℕ)^4823*50000000000000000000^1024 ≤ 9767520580716191^1024*100000^4823 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16311 100000 9767520580716191 50000000000000000000 4823 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16311/100000 : ℝ)) (X := (9767520580716191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000500075466413477/10000000000000000000 : ℝ) ≤ (5000053085962317/5000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (10000500075466413477/10000000000000000000 : ℝ)^1024 ≤ (5000053085962317/5000000000000000 : ℝ)^4823 := by
      have hnat : (10000500075466413477 : ℕ)^1024*5000000000000000^4823 ≤ 5000053085962317^4823*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000500075466413477 10000000000000000000 5000053085962317 5000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000053085962317/5000000000000000 : ℝ)) (X := (10000500075466413477/10000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022035418493499767/100000000000000000000 : ℝ) ≤ (5000233903281779/5000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (100022035418493499767/100000000000000000000 : ℝ)^1024 ≤ (5000233903281779/5000000000000000 : ℝ)^4823 := by
      have hnat : (100022035418493499767 : ℕ)^1024*5000000000000000^4823 ≤ 5000233903281779^4823*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022035418493499767 100000000000000000000 5000233903281779 5000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000233903281779/5000000000000000 : ℝ)) (X := (100022035418493499767/100000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009767520580716191/25000000000000000000 : ℝ) ≤ (5000414720601241/5000000000000000 : ℝ) ^ (4823/1024 : ℝ) := by
    have hpowers : (25009767520580716191/25000000000000000000 : ℝ)^1024 ≤ (5000414720601241/5000000000000000 : ℝ)^4823 := by
      have hnat : (25009767520580716191 : ℕ)^1024*5000000000000000^4823 ≤ 5000414720601241^4823*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009767520580716191 25000000000000000000 5000414720601241 5000000000000000 1024 4823 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000414720601241/5000000000000000 : ℝ)) (X := (25009767520580716191/25000000000000000000 : ℝ)) (by norm_num) 4823 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(500075466413477/20000000000000000000 : ℝ) ≤ ((1922766260036871331/1923000000000000000 : ℝ)+2*(90408659731/144225000000000 : ℝ)*(5271/50000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (1922766260036871331/1923000000000000000 : ℝ)+2*(90408659731/144225000000000 : ℝ)*(5271/50000 : ℝ)=(5000053085962317/5000000000000000 : ℝ) by norm_num, show 1+2*(500075466413477/20000000000000000000 : ℝ)=(10000500075466413477/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9767520580716191/50000000000000000000 : ℝ)+(500075466413477/20000000000000000000 : ℝ) ≤ ((1922766260036871331/1923000000000000000 : ℝ)+(90408659731/144225000000000 : ℝ)*((16311/100000 : ℝ)+(5271/50000 : ℝ)))^(4823/1024 : ℝ) := by
    rw [show (1922766260036871331/1923000000000000000 : ℝ)+(90408659731/144225000000000 : ℝ)*((16311/100000 : ℝ)+(5271/50000 : ℝ))=(5000233903281779/5000000000000000 : ℝ) by norm_num, show 1+(9767520580716191/50000000000000000000 : ℝ)+(500075466413477/20000000000000000000 : ℝ)=(100022035418493499767/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9767520580716191/50000000000000000000 : ℝ) ≤ ((1922766260036871331/1923000000000000000 : ℝ)+2*(90408659731/144225000000000 : ℝ)*(16311/100000 : ℝ))^(4823/1024 : ℝ) := by
    rw [show (1922766260036871331/1923000000000000000 : ℝ)+2*(90408659731/144225000000000 : ℝ)*(16311/100000 : ℝ)=(5000414720601241/5000000000000000 : ℝ) by norm_num, show 1+2*(9767520580716191/50000000000000000000 : ℝ)=(25009767520580716191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1922766260036871331/1923000000000000000 : ℝ)*(X 1 0+X 2 0)+(90408659731/144225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (16311/100000 : ℝ)) (c := (1922766260036871331/1923000000000000000 : ℝ)) (alpha := (90408659731/144225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1922766260036871331/1923000000000000000 : ℝ)*(X 0 1+X 2 1)+(90408659731/144225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (16311/100000 : ℝ)) (c := (1922766260036871331/1923000000000000000 : ℝ)) (alpha := (90408659731/144225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1922766260036871331/1923000000000000000 : ℝ)*(X 0 2+X 1 2)+(90408659731/144225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4823/1024 : ℝ)) (lo := (5271/50000 : ℝ)) (hi := (16311/100000 : ℝ)) (c := (1922766260036871331/1923000000000000000 : ℝ)) (alpha := (90408659731/144225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87242839/625000000 : ℝ)*X 0 0+(1353446417/2500000000 : ℝ)*X 0 1+(5413784403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251254759/10000000000 : ℝ)*X 1 0+(-101513181/625000000 : ℝ)*X 1 1+(5413784107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625626837/5000000000 : ℝ)*X 2 0+(1082757043/2000000000 : ℝ)*X 2 1+(-406052713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4477207643/10000000000 : ℝ)*X 0 0+(4071941799/10000000000 : ℝ)*X 0 1+(2035970499/5000000000 : ℝ)*X 0 2+(4477207643/10000000000 : ℝ)*X 1 0+(4071941799/10000000000 : ℝ)*X 1 1+(2035970499/5000000000 : ℝ)*X 1 2+(4477207643/10000000000 : ℝ)*X 2 0+(4071941799/10000000000 : ℝ)*X 2 1+(2035970499/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1939645233/10000000000 : ℝ)*X 0 0+(5214957287/10000000000 : ℝ)*X 0 1+(1303739239/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((673519273/1250000000 : ℝ)*X 1 0+(-1708785039/10000000000 : ℝ)*X 1 1+(325934801/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5388153961/10000000000 : ℝ)*X 2 0+(5214957113/10000000000 : ℝ)*X 2 1+(-854392471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3914149321/10000000000 : ℝ)*X 0 0+(1088283847/2500000000 : ℝ)*X 0 1+(1088283867/2500000000 : ℝ)*X 0 2+(3914149321/10000000000 : ℝ)*X 1 0+(1088283847/2500000000 : ℝ)*X 1 1+(1088283867/2500000000 : ℝ)*X 1 2+(3914149321/10000000000 : ℝ)*X 2 0+(1088283847/2500000000 : ℝ)*X 2 1+(1088283867/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-455965319/2500000000 : ℝ)*X 0 0+(202900757/400000000 : ℝ)*X 0 1+(5443524023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615387891/5000000000 : ℝ)*X 1 0+(-20138917/125000000 : ℝ)*X 1 1+(5443523931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((326923477/625000000 : ℝ)*X 2 0+(5443523931/10000000000 : ℝ)*X 2 1+(-805556783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4559036387/10000000000 : ℝ)*X 0 0+(4029806679/10000000000 : ℝ)*X 0 1+(402980659/1000000000 : ℝ)*X 0 2+(4559036387/10000000000 : ℝ)*X 1 0+(4029806679/10000000000 : ℝ)*X 1 1+(402980659/1000000000 : ℝ)*X 1 2+(4559036387/10000000000 : ℝ)*X 2 0+(4029806679/10000000000 : ℝ)*X 2 1+(402980659/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-23596913/156250000 : ℝ)*X 0 0+(173455883/312500000 : ℝ)*X 0 1+(1298774593/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5401835177/10000000000 : ℝ)*X 1 0+(-1716938469/10000000000 : ℝ)*X 1 1+(519509853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1350458787/2500000000 : ℝ)*X 2 0+(5195098699/10000000000 : ℝ)*X 2 1+(-42923457/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1928142841/5000000000 : ℝ)*X 0 0+(1095292573/2500000000 : ℝ)*X 0 1+(4381170647/10000000000 : ℝ)*X 0 2+(1928142841/5000000000 : ℝ)*X 1 0+(1095292573/2500000000 : ℝ)*X 1 1+(4381170647/10000000000 : ℝ)*X 1 2+(1928142841/5000000000 : ℝ)*X 2 0+(1095292573/2500000000 : ℝ)*X 2 1+(4381170647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1627_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64977/100000 : ℝ) ≤ (-62473429886565084876502834823581/96150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51646583/25000000000000 : ℝ)*(lower2) + (11074677/20000000000000 : ℝ)*(lower3) + (216941027/100000000000000 : ℝ)*(lower4) + (10137561/20000000000000 : ℝ)*(lower5) + (1714835799125083/100000000000000 : ℝ)*(major0) + (1714835799125083/100000000000000 : ℝ)*(major1) + (1714835799125083/100000000000000 : ℝ)*(major2) + (345140561/25000000000000 : ℝ)*(sp1) + (2474891288910739/100000000000000 : ℝ)*(sp4) + (1237446008005483/50000000000000 : ℝ)*(sp5) + (2474874439440549/100000000000000 : ℝ)*(sp6) + (976436523703839/100000000000000 : ℝ)*(sp7) + (2107662471/100000000000000 : ℝ)*(sp8) + (9478566331/50000000000000 : ℝ)*(sp14) + (976436523703839/100000000000000 : ℝ)*(f.failure) + (247489339657321/10000000000000 : ℝ)*(f.sum) + (132133357780693/7211250000000000000000000000 : ℝ)*base65 + (2912512744874006419/576900000000000000000000000000000 : ℝ)*base67 + (1647379661172093581/576900000000000000000000000000000 : ℝ)*base70 + (13717391816373093581/576900000000000000000000000000000 : ℝ)*base72 + (2302810144519/14422500000000000000000000000 : ℝ)*base74 + (493664089613606419/576900000000000000000000000000000 : ℝ)*base75 + (3486224709235593581/576900000000000000000000000000000 : ℝ)*base78 + (303366118864293581/576900000000000000000000000000000 : ℝ)*base80 + (15377396274769/14422500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (43947599/10000000000000000000000 : ℝ)*base89 + (43947599/10000000000000000000000 : ℝ)*base91 + (43947599/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29189/50000 : ℝ) ≤ (9355423765828554298078541169031/16025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48048541/100000000000000 : ℝ)*(upper2) + (31916629/100000000000000 : ℝ)*(upper3) + (9131497/5000000000000 : ℝ)*(lower5) + (1802013722473299/100000000000000 : ℝ)*(major0) + (1802013722473299/100000000000000 : ℝ)*(major1) + (1802013722473299/100000000000000 : ℝ)*(major2) + (39976359496987/1562500000000 : ℝ)*(sp0) + (255845081126369/10000000000000 : ℝ)*(sp1) + (255848058152859/10000000000000 : ℝ)*(sp2) + (256518351354523/25000000000000 : ℝ)*(sp3) + (10711786507/100000000000000 : ℝ)*(sp6) + (2686378087/100000000000000 : ℝ)*(sp7) + (535688491/12500000000000 : ℝ)*(sp8) + (40482051407/100000000000000 : ℝ)*(sp9) + (1026076091796179/100000000000000 : ℝ)*(f.failure) + (319811411664387/12500000000000 : ℝ)*(f.sum) + (73697375271553/9615000000000000000000000000 : ℝ)*base66 + (1204399242184610969/192300000000000000000000000000000 : ℝ)*base67 + (697360929913010969/192300000000000000000000000000000 : ℝ)*base69 + (201640088962910969/192300000000000000000000000000000 : ℝ)*base71 + (5665997876467/2403750000000000000000000000 : ℝ)*base74 + (830059333495310969/192300000000000000000000000000000 : ℝ)*base75 + (475432423783989031/192300000000000000000000000000000 : ℝ)*base78 + (816863683265510969/192300000000000000000000000000000 : ℝ)*base79 + (22463198342789/4807500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (52745539/10000000000000000000000 : ℝ)*base89 + (52745539/10000000000000000000000 : ℝ)*base91 + (52745539/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80767/100000 : ℝ) ≤ (485372143168635583705879851539/600937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (31582273/100000000000000 : ℝ)*(upper1) + (32037589/50000000000000 : ℝ)*(upper2) + (18465463/100000000000000 : ℝ)*(lower5) + (2973312527621/156250000000 : ℝ)*(major0) + (2973312527621/156250000000 : ℝ)*(major1) + (2973312527621/156250000000 : ℝ)*(major2) + (34073287211/100000000000000 : ℝ)*(sp1) + (11264307677/50000000000000 : ℝ)*(sp2) + (8660219663/100000000000000 : ℝ)*(sp3) + (165463241/4000000000000 : ℝ)*(sp4) + (336922522493209/12500000000000 : ℝ)*(sp8) + (1347675121619743/50000000000000 : ℝ)*(sp9) + (168460111744459/6250000000000 : ℝ)*(sp10) + (1083524006812019/100000000000000 : ℝ)*(sp11) + (541766333515841/50000000000000 : ℝ)*(f.failure) + (1347692158263349/50000000000000 : ℝ)*(f.sum) + (9893368512773/5769000000000000000000000000 : ℝ)*base66 + (44438982185689487/3605625000000000000000000000000 : ℝ)*base67 + (8446183078459403/901406250000000000000000000000 : ℝ)*base69 + (40927664290658237/3605625000000000000000000000000 : ℝ)*base71 + (3680952575297/2884500000000000000000000000 : ℝ)*base73 + (32288193546773237/3605625000000000000000000000000 : ℝ)*base75 + (13136544473920681/1802812500000000000000000000000 : ℝ)*base77 + (352546909052191/112675781250000000000000000000 : ℝ)*base79 + (2704413952739/1442250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (916719/5000000000000000000000 : ℝ)*base90 + (916719/5000000000000000000000 : ℝ)*base92 + (916719/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-87997/100000 : ℝ) ≤ (-141010480007333965344911433177/160250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56527859/100000000000000 : ℝ)*(lower0) + (23677229/20000000000000 : ℝ)*(lower1) + (43253661/100000000000000 : ℝ)*(lower2) + (19458293883317/1000000000000 : ℝ)*(major0) + (19458293883317/1000000000000 : ℝ)*(major1) + (19458293883317/1000000000000 : ℝ)*(major2) + (2047500367/50000000000000 : ℝ)*(sp0) + (16465902569/20000000000000 : ℝ)*(sp5) + (44750149611/100000000000000 : ℝ)*(sp6) + (50041827/800000000000 : ℝ)*(sp7) + (1406510273190833/50000000000000 : ℝ)*(sp12) + (1406471155934777/50000000000000 : ℝ)*(sp13) + (703244972808197/25000000000000 : ℝ)*(sp14) + (1107959233148267/100000000000000 : ℝ)*(sp15) + (553982744188321/50000000000000 : ℝ)*(f.failure) + (54941887527/1953125000 : ℝ)*(f.sum) + (7605325329869/5769000000000000000000000000 : ℝ)*base66 + (26845396012366781/5769000000000000000000000000000 : ℝ)*base67 + (6551729728027781/5769000000000000000000000000000 : ℝ)*base69 + (1971207440848219/5769000000000000000000000000000 : ℝ)*base72 + (14830107166933/5769000000000000000000000000 : ℝ)*base73 + (46937858914393781/5769000000000000000000000000000 : ℝ)*base75 + (2530359083518781/5769000000000000000000000000000 : ℝ)*base77 + (99698744952223781/5769000000000000000000000000000 : ℝ)*base79 + (10097096318017/5769000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15281039/5000000000000000000000 : ℝ)*base90 + (15281039/5000000000000000000000 : ℝ)*base92 + (15281039/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1627_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64977/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29189/50000 : ℝ) else (80767/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87997/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1627_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1627_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64977/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29189/50000 : ℝ) else (80767/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87997/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1627_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4823/1024 : ℝ) ≤ p) (hpb : p ≤ (4827/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (175621841/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16311/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5271/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64977/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29189/50000 : ℝ) else (80767/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87997/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1627_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
