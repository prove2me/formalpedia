-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1608_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:59.345907+00:00
-- url     : https://prove2.me/submissions/90c911d0-9ef1-4bb5-8682-fd731a10c937

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
theorem support_rectangle_w1608_s3_0 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85460351/500000000 : ℝ)*x 0 + (43685343/80000000 : ℝ)*x 1 + (647510613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85460351/500000000 : ℝ)^4751 ≤ (10519706262897/100000000000000 : ℝ)^3727 := by
    have hnat : (85460351 : ℕ)^4751*100000000000000^3727 ≤ 10519706262897^3727*500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85460351 500000000 10519706262897 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43685343/80000000 : ℝ)^4751 ≤ (46243804923923/100000000000000 : ℝ)^3727 := by
    have hnat : (43685343 : ℕ)^4751*100000000000000^3727 ≤ 46243804923923^3727*80000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43685343 80000000 46243804923923 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647510613/1250000000 : ℝ)^4751 ≤ (21618244398433/50000000000000 : ℝ)^3727 := by
    have hnat : (647510613 : ℕ)^4751*50000000000000^3727 ≤ 21618244398433^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647510613 1250000000 21618244398433 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85460351/500000000 : ℝ), (43685343/80000000 : ℝ), (647510613/1250000000 : ℝ)] ![(10519706262897/100000000000000 : ℝ), (46243804923923/100000000000000 : ℝ), (21618244398433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85460351/500000000 : ℝ)|^4751 ≤ (10519706262897/100000000000000 : ℝ)^3727
        have hw : |(-85460351/500000000 : ℝ)|=(85460351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43685343/80000000 : ℝ)|^4751 ≤ (46243804923923/100000000000000 : ℝ)^3727
        have hw : |(43685343/80000000 : ℝ)|=(43685343/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647510613/1250000000 : ℝ)|^4751 ≤ (21618244398433/50000000000000 : ℝ)^3727
        have hw : |(647510613/1250000000 : ℝ)|=(647510613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_1 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669250977/1250000000 : ℝ)*x 0 + (-1853919647/10000000000 : ℝ)*x 1 + (2590042233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669250977/1250000000 : ℝ)^4751 ≤ (45095485294829/100000000000000 : ℝ)^3727 := by
    have hnat : (669250977 : ℕ)^4751*100000000000000^3727 ≤ 45095485294829^3727*1250000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669250977 1250000000 45095485294829 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853919647/10000000000 : ℝ)^4751 ≤ (466721222527/4000000000000 : ℝ)^3727 := by
    have hnat : (1853919647 : ℕ)^4751*4000000000000^3727 ≤ 466721222527^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853919647 10000000000 466721222527 4000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590042233/5000000000 : ℝ)^4751 ≤ (43236484136573/100000000000000 : ℝ)^3727 := by
    have hnat : (2590042233 : ℕ)^4751*100000000000000^3727 ≤ 43236484136573^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590042233 5000000000 43236484136573 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669250977/1250000000 : ℝ), (-1853919647/10000000000 : ℝ), (2590042233/5000000000 : ℝ)] ![(45095485294829/100000000000000 : ℝ), (466721222527/4000000000000 : ℝ), (43236484136573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669250977/1250000000 : ℝ)|^4751 ≤ (45095485294829/100000000000000 : ℝ)^3727
        have hw : |(669250977/1250000000 : ℝ)|=(669250977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853919647/10000000000 : ℝ)|^4751 ≤ (466721222527/4000000000000 : ℝ)^3727
        have hw : |(-1853919647/10000000000 : ℝ)|=(1853919647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590042233/5000000000 : ℝ)|^4751 ≤ (43236484136573/100000000000000 : ℝ)^3727
        have hw : |(2590042233/5000000000 : ℝ)|=(2590042233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_2 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354007693/10000000000 : ℝ)*x 0 + (5180084613/10000000000 : ℝ)*x 1 + (-14483747/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354007693/10000000000 : ℝ)^4751 ≤ (11273870993547/25000000000000 : ℝ)^3727 := by
    have hnat : (5354007693 : ℕ)^4751*25000000000000^3727 ≤ 11273870993547^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354007693 10000000000 11273870993547 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180084613/10000000000 : ℝ)^4751 ≤ (10809121425161/25000000000000 : ℝ)^3727 := by
    have hnat : (5180084613 : ℕ)^4751*25000000000000^3727 ≤ 10809121425161^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180084613 10000000000 10809121425161 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14483747/78125000 : ℝ)^4751 ≤ (364625947327/3125000000000 : ℝ)^3727 := by
    have hnat : (14483747 : ℕ)^4751*3125000000000^3727 ≤ 364625947327^3727*78125000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14483747 78125000 364625947327 3125000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354007693/10000000000 : ℝ), (5180084613/10000000000 : ℝ), (-14483747/78125000 : ℝ)] ![(11273870993547/25000000000000 : ℝ), (10809121425161/25000000000000 : ℝ), (364625947327/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354007693/10000000000 : ℝ)|^4751 ≤ (11273870993547/25000000000000 : ℝ)^3727
        have hw : |(5354007693/10000000000 : ℝ)|=(5354007693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180084613/10000000000 : ℝ)|^4751 ≤ (10809121425161/25000000000000 : ℝ)^3727
        have hw : |(5180084613/10000000000 : ℝ)|=(5180084613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14483747/78125000 : ℝ)|^4751 ≤ (364625947327/3125000000000 : ℝ)^3727
        have hw : |(-14483747/78125000 : ℝ)|=(14483747/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_3 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131691193/312500000 : ℝ)*x 0 + (1940558363/5000000000 : ℝ)*x 1 + (456879023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131691193/312500000 : ℝ)^4751 ≤ (33234886447281/100000000000000 : ℝ)^3727 := by
    have hnat : (131691193 : ℕ)^4751*100000000000000^3727 ≤ 33234886447281^3727*312500000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131691193 312500000 33234886447281 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1940558363/5000000000 : ℝ)^4751 ≤ (29924149418861/100000000000000 : ℝ)^3727 := by
    have hnat : (1940558363 : ℕ)^4751*100000000000000^3727 ≤ 29924149418861^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940558363 5000000000 29924149418861 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456879023/1000000000 : ℝ)^4751 ≤ (36840964121757/100000000000000 : ℝ)^3727 := by
    have hnat : (456879023 : ℕ)^4751*100000000000000^3727 ≤ 36840964121757^3727*1000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456879023 1000000000 36840964121757 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131691193/312500000 : ℝ), (1940558363/5000000000 : ℝ), (456879023/1000000000 : ℝ)] ![(33234886447281/100000000000000 : ℝ), (29924149418861/100000000000000 : ℝ), (36840964121757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131691193/312500000 : ℝ)|^4751 ≤ (33234886447281/100000000000000 : ℝ)^3727
        have hw : |(131691193/312500000 : ℝ)|=(131691193/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1940558363/5000000000 : ℝ)|^4751 ≤ (29924149418861/100000000000000 : ℝ)^3727
        have hw : |(1940558363/5000000000 : ℝ)|=(1940558363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(456879023/1000000000 : ℝ)|^4751 ≤ (36840964121757/100000000000000 : ℝ)^3727
        have hw : |(456879023/1000000000 : ℝ)|=(456879023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_4 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1709278597/10000000000 : ℝ)*x 0 + (64777201/125000000 : ℝ)*x 1 + (5458554541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1709278597/10000000000 : ℝ)^4751 ≤ (10520267841527/100000000000000 : ℝ)^3727 := by
    have hnat : (1709278597 : ℕ)^4751*100000000000000^3727 ≤ 10520267841527^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709278597 10000000000 10520267841527 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64777201/125000000 : ℝ)^4751 ≤ (8651748003557/20000000000000 : ℝ)^3727 := by
    have hnat : (64777201 : ℕ)^4751*20000000000000^3727 ≤ 8651748003557^3727*125000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64777201 125000000 8651748003557 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458554541/10000000000 : ℝ)^4751 ≤ (46220992129707/100000000000000 : ℝ)^3727 := by
    have hnat : (5458554541 : ℕ)^4751*100000000000000^3727 ≤ 46220992129707^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458554541 10000000000 46220992129707 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1709278597/10000000000 : ℝ), (64777201/125000000 : ℝ), (5458554541/10000000000 : ℝ)] ![(10520267841527/100000000000000 : ℝ), (8651748003557/20000000000000 : ℝ), (46220992129707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1709278597/10000000000 : ℝ)|^4751 ≤ (10520267841527/100000000000000 : ℝ)^3727
        have hw : |(-1709278597/10000000000 : ℝ)|=(1709278597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64777201/125000000 : ℝ)|^4751 ≤ (8651748003557/20000000000000 : ℝ)^3727
        have hw : |(64777201/125000000 : ℝ)|=(64777201/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458554541/10000000000 : ℝ)|^4751 ≤ (46220992129707/100000000000000 : ℝ)^3727
        have hw : |(5458554541/10000000000 : ℝ)|=(5458554541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_5 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279517893/10000000000 : ℝ)*x 0 + (-31508999/200000000 : ℝ)*x 1 + (1364638559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279517893/10000000000 : ℝ)^4751 ≤ (44297226795723/100000000000000 : ℝ)^3727 := by
    have hnat : (5279517893 : ℕ)^4751*100000000000000^3727 ≤ 44297226795723^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279517893 10000000000 44297226795723 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31508999/200000000 : ℝ)^4751 ≤ (9481784356649/100000000000000 : ℝ)^3727 := by
    have hnat : (31508999 : ℕ)^4751*100000000000000^3727 ≤ 9481784356649^3727*200000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31508999 200000000 9481784356649 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364638559/2500000000 : ℝ)^4751 ≤ (3697679107/8000000000 : ℝ)^3727 := by
    have hnat : (1364638559 : ℕ)^4751*8000000000^3727 ≤ 3697679107^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364638559 2500000000 3697679107 8000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279517893/10000000000 : ℝ), (-31508999/200000000 : ℝ), (1364638559/2500000000 : ℝ)] ![(44297226795723/100000000000000 : ℝ), (9481784356649/100000000000000 : ℝ), (3697679107/8000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279517893/10000000000 : ℝ)|^4751 ≤ (44297226795723/100000000000000 : ℝ)^3727
        have hw : |(5279517893/10000000000 : ℝ)|=(5279517893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31508999/200000000 : ℝ)|^4751 ≤ (9481784356649/100000000000000 : ℝ)^3727
        have hw : |(-31508999/200000000 : ℝ)|=(31508999/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364638559/2500000000 : ℝ)|^4751 ≤ (3697679107/8000000000 : ℝ)^3727
        have hw : |(1364638559/2500000000 : ℝ)|=(1364638559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_6 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639758793/5000000000 : ℝ)*x 0 + (1091710883/2000000000 : ℝ)*x 1 + (-393862531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639758793/5000000000 : ℝ)^4751 ≤ (44297223512153/100000000000000 : ℝ)^3727 := by
    have hnat : (2639758793 : ℕ)^4751*100000000000000^3727 ≤ 44297223512153^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639758793 5000000000 44297223512153 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091710883/2000000000 : ℝ)^4751 ≤ (2888811923103/6250000000000 : ℝ)^3727 := by
    have hnat : (1091710883 : ℕ)^4751*6250000000000^3727 ≤ 2888811923103^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091710883 2000000000 2888811923103 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393862531/2500000000 : ℝ)^4751 ≤ (148152901431/1562500000000 : ℝ)^3727 := by
    have hnat : (393862531 : ℕ)^4751*1562500000000^3727 ≤ 148152901431^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393862531 2500000000 148152901431 1562500000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639758793/5000000000 : ℝ), (1091710883/2000000000 : ℝ), (-393862531/2500000000 : ℝ)] ![(44297223512153/100000000000000 : ℝ), (2888811923103/6250000000000 : ℝ), (148152901431/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639758793/5000000000 : ℝ)|^4751 ≤ (44297223512153/100000000000000 : ℝ)^3727
        have hw : |(2639758793/5000000000 : ℝ)|=(2639758793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091710883/2000000000 : ℝ)|^4751 ≤ (2888811923103/6250000000000 : ℝ)^3727
        have hw : |(1091710883/2000000000 : ℝ)|=(1091710883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393862531/2500000000 : ℝ)|^4751 ≤ (148152901431/1562500000000 : ℝ)^3727
        have hw : |(-393862531/2500000000 : ℝ)|=(393862531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s3_7 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2107146899/5000000000 : ℝ)*x 0 + (4563663621/10000000000 : ℝ)*x 1 + (777259383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107146899/5000000000 : ℝ)^4751 ≤ (2077290753517/6250000000000 : ℝ)^3727 := by
    have hnat : (2107146899 : ℕ)^4751*6250000000000^3727 ≤ 2077290753517^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107146899 5000000000 2077290753517 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4563663621/10000000000 : ℝ)^4751 ≤ (36788275282307/100000000000000 : ℝ)^3727 := by
    have hnat : (4563663621 : ℕ)^4751*100000000000000^3727 ≤ 36788275282307^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563663621 10000000000 36788275282307 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777259383/2000000000 : ℝ)^4751 ≤ (29975072649893/100000000000000 : ℝ)^3727 := by
    have hnat : (777259383 : ℕ)^4751*100000000000000^3727 ≤ 29975072649893^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777259383 2000000000 29975072649893 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107146899/5000000000 : ℝ), (4563663621/10000000000 : ℝ), (777259383/2000000000 : ℝ)] ![(2077290753517/6250000000000 : ℝ), (36788275282307/100000000000000 : ℝ), (29975072649893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107146899/5000000000 : ℝ)|^4751 ≤ (2077290753517/6250000000000 : ℝ)^3727
        have hw : |(2107146899/5000000000 : ℝ)|=(2107146899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4563663621/10000000000 : ℝ)|^4751 ≤ (36788275282307/100000000000000 : ℝ)^3727
        have hw : |(4563663621/10000000000 : ℝ)|=(4563663621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(777259383/2000000000 : ℝ)|^4751 ≤ (29975072649893/100000000000000 : ℝ)^3727
        have hw : |(777259383/2000000000 : ℝ)|=(777259383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1608_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (1041/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8179/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8251/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (257/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8251/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (257/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8251/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (257/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8251/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (257/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8251/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (257/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8251/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (257/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (257/2500 : ℝ) ^ (4747/1024 : ℝ) ≤ (2629388747818011/100000000000000000000 : ℝ) := by
    have hpowers : (257/2500 : ℝ)^4747 ≤ (2629388747818011/100000000000000000000 : ℝ)^1024 := by
      have hnat : (257 : ℕ)^4747*100000000000000000000^1024 ≤ 2629388747818011^1024*2500^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        257 2500 2629388747818011 100000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (257/2500 : ℝ)) (X := (2629388747818011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8251/50000 : ℝ) ^ (4747/1024 : ℝ) ≤ (5897138602687669/25000000000000000000 : ℝ) := by
    have hpowers : (8251/50000 : ℝ)^4747 ≤ (5897138602687669/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8251 : ℕ)^4747*25000000000000000000^1024 ≤ 5897138602687669^1024*50000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8251 50000 5897138602687669 25000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8251/50000 : ℝ)) (X := (5897138602687669/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002629388747818011/50000000000000000000 : ℝ) ≤ (5000056718739313/5000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (50002629388747818011/50000000000000000000 : ℝ)^1024 ≤ (5000056718739313/5000000000000000 : ℝ)^4747 := by
      have hnat : (50002629388747818011 : ℕ)^1024*5000000000000000^4747 ≤ 5000056718739313^4747*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002629388747818011 50000000000000000000 5000056718739313 5000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000056718739313/5000000000000000 : ℝ)) (X := (50002629388747818011/50000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026217943158568687/100000000000000000000 : ℝ) ≤ (10000565502717967/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (100026217943158568687/100000000000000000000 : ℝ)^1024 ≤ (10000565502717967/10000000000000000 : ℝ)^4747 := by
      have hnat : (100026217943158568687 : ℕ)^1024*10000000000000000^4747 ≤ 10000565502717967^4747*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026217943158568687 100000000000000000000 10000565502717967 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000565502717967/10000000000000000 : ℝ)) (X := (100026217943158568687/100000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505897138602687669/12500000000000000000 : ℝ) ≤ (2500254391989327/2500000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (12505897138602687669/12500000000000000000 : ℝ)^1024 ≤ (2500254391989327/2500000000000000 : ℝ)^4747 := by
      have hnat : (12505897138602687669 : ℕ)^1024*2500000000000000^4747 ≤ 2500254391989327^4747*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505897138602687669 12500000000000000000 2500254391989327 2500000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500254391989327/2500000000000000 : ℝ)) (X := (12505897138602687669/12500000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2629388747818011/100000000000000000000 : ℝ) ≤ ((15552852836667790003/15555000000000000000 : ℝ)+2*(452065239341/622200000000000 : ℝ)*(257/2500 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (15552852836667790003/15555000000000000000 : ℝ)+2*(452065239341/622200000000000 : ℝ)*(257/2500 : ℝ)=(5000056718739313/5000000000000000 : ℝ) by norm_num, show 1+2*(2629388747818011/100000000000000000000 : ℝ)=(50002629388747818011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5897138602687669/25000000000000000000 : ℝ)+(2629388747818011/100000000000000000000 : ℝ) ≤ ((15552852836667790003/15555000000000000000 : ℝ)+(452065239341/622200000000000 : ℝ)*((8251/50000 : ℝ)+(257/2500 : ℝ)))^(4747/1024 : ℝ) := by
    rw [show (15552852836667790003/15555000000000000000 : ℝ)+(452065239341/622200000000000 : ℝ)*((8251/50000 : ℝ)+(257/2500 : ℝ))=(10000565502717967/10000000000000000 : ℝ) by norm_num, show 1+(5897138602687669/25000000000000000000 : ℝ)+(2629388747818011/100000000000000000000 : ℝ)=(100026217943158568687/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5897138602687669/25000000000000000000 : ℝ) ≤ ((15552852836667790003/15555000000000000000 : ℝ)+2*(452065239341/622200000000000 : ℝ)*(8251/50000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (15552852836667790003/15555000000000000000 : ℝ)+2*(452065239341/622200000000000 : ℝ)*(8251/50000 : ℝ)=(2500254391989327/2500000000000000 : ℝ) by norm_num, show 1+2*(5897138602687669/25000000000000000000 : ℝ)=(12505897138602687669/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15552852836667790003/15555000000000000000 : ℝ)*(X 1 0+X 2 0)+(452065239341/622200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (257/2500 : ℝ)) (hi := (8251/50000 : ℝ)) (c := (15552852836667790003/15555000000000000000 : ℝ)) (alpha := (452065239341/622200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15552852836667790003/15555000000000000000 : ℝ)*(X 0 1+X 2 1)+(452065239341/622200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (257/2500 : ℝ)) (hi := (8251/50000 : ℝ)) (c := (15552852836667790003/15555000000000000000 : ℝ)) (alpha := (452065239341/622200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15552852836667790003/15555000000000000000 : ℝ)*(X 0 2+X 1 2)+(452065239341/622200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (257/2500 : ℝ)) (hi := (8251/50000 : ℝ)) (c := (15552852836667790003/15555000000000000000 : ℝ)) (alpha := (452065239341/622200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85460351/500000000 : ℝ)*X 0 0+(43685343/80000000 : ℝ)*X 0 1+(647510613/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669250977/1250000000 : ℝ)*X 1 0+(-1853919647/10000000000 : ℝ)*X 1 1+(2590042233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354007693/10000000000 : ℝ)*X 2 0+(5180084613/10000000000 : ℝ)*X 2 1+(-14483747/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((131691193/312500000 : ℝ)*X 0 0+(1940558363/5000000000 : ℝ)*X 0 1+(456879023/1000000000 : ℝ)*X 0 2+(131691193/312500000 : ℝ)*X 1 0+(1940558363/5000000000 : ℝ)*X 1 1+(456879023/1000000000 : ℝ)*X 1 2+(131691193/312500000 : ℝ)*X 2 0+(1940558363/5000000000 : ℝ)*X 2 1+(456879023/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1709278597/10000000000 : ℝ)*X 0 0+(64777201/125000000 : ℝ)*X 0 1+(5458554541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279517893/10000000000 : ℝ)*X 1 0+(-31508999/200000000 : ℝ)*X 1 1+(1364638559/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639758793/5000000000 : ℝ)*X 2 0+(1091710883/2000000000 : ℝ)*X 2 1+(-393862531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2107146899/5000000000 : ℝ)*X 0 0+(4563663621/10000000000 : ℝ)*X 0 1+(777259383/2000000000 : ℝ)*X 0 2+(2107146899/5000000000 : ℝ)*X 1 0+(4563663621/10000000000 : ℝ)*X 1 1+(777259383/2000000000 : ℝ)*X 1 2+(2107146899/5000000000 : ℝ)*X 2 0+(4563663621/10000000000 : ℝ)*X 2 1+(777259383/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (196108666680017213903629329/32406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54416831/5000000000000 : ℝ)*(base19) + (124833549/12500000000000 : ℝ)*(base23) + (5580879/5000000000000 : ℝ)*(upper3) + (1042731/25000000000000 : ℝ)*(upper4) + (58374627/50000000000000 : ℝ)*(upper5) + (313638418926057/12500000000000 : ℝ)*(major0) + (313638418926057/12500000000000 : ℝ)*(major1) + (313638418926057/12500000000000 : ℝ)*(major2) + (891004348928271/25000000000000 : ℝ)*(sp0) + (1782012765449773/50000000000000 : ℝ)*(sp1) + (1782012810283887/50000000000000 : ℝ)*(sp2) + (727091607986937/50000000000000 : ℝ)*(sp3) + (9223523083/100000000000000 : ℝ)*(sp4) + (4665887889/100000000000000 : ℝ)*(sp7) + (1454187881861763/100000000000000 : ℝ)*(f.failure) + (1782013309618083/50000000000000 : ℝ)*(f.sum) + (8639881530141/5185000000000000000000000000 : ℝ)*base65 + (2140620796151443/64812500000000000000000000000000 : ℝ)*base68 + (31593595968463943/64812500000000000000000000000000 : ℝ)*base70 + (514365484278036057/64812500000000000000000000000000 : ℝ)*base71 + (15143092908319/5185000000000000000000000000 : ℝ)*base74 + (501852257463473557/64812500000000000000000000000000 : ℝ)*base75 + (369896228134161057/64812500000000000000000000000000 : ℝ)*base77 + (785031151459223557/64812500000000000000000000000000 : ℝ)*base79 + (1690798831219/5185000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (48306639/10000000000000000000000 : ℝ)*base90 + (48306639/10000000000000000000000 : ℝ)*base92 + (48306639/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (476223893933005713569482981/64812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1366249331/100000000000000 : ℝ)*(base19) + (1149216969/100000000000000 : ℝ)*(base23) + (126775031/100000000000000 : ℝ)*(upper3) + (3154863/10000000000000 : ℝ)*(lower4) + (279930717/100000000000000 : ℝ)*(upper5) + (1273633171521827/50000000000000 : ℝ)*(major0) + (1273633171521827/50000000000000 : ℝ)*(major1) + (1273633171521827/50000000000000 : ℝ)*(major2) + (275321597/2000000000000 : ℝ)*(sp1) + (9060500307/100000000000000 : ℝ)*(sp2) + (3618228987726431/100000000000000 : ℝ)*(sp4) + (14472855421589/400000000000 : ℝ)*(sp5) + (1809109389004577/50000000000000 : ℝ)*(sp6) + (738151726718489/50000000000000 : ℝ)*(sp7) + (738151726718489/50000000000000 : ℝ)*(f.failure) + (3618228987726431/100000000000000 : ℝ)*(f.sum) + (4882065972493/3888750000000000000000000000 : ℝ)*base65 + (437462239394143173/259250000000000000000000000000000 : ℝ)*base68 + (2336506916206893173/259250000000000000000000000000000 : ℝ)*base70 + (1649926910797143173/259250000000000000000000000000000 : ℝ)*base72 + (33270145853167/15555000000000000000000000000 : ℝ)*base73 + (1286567211800143173/259250000000000000000000000000000 : ℝ)*base76 + (649414311888393173/259250000000000000000000000000000 : ℝ)*base78 + (978659614611606827/259250000000000000000000000000000 : ℝ)*base79 + (131585458276403/15555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (62540483/5000000000000000000000 : ℝ)*base89 + (62540483/5000000000000000000000 : ℝ)*base91 + (62540483/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1608_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1041/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1608_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1608_s4_0 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-854664067/5000000000 : ℝ)*x 0 + (1092011701/2000000000 : ℝ)*x 1 + (1295153461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854664067/5000000000 : ℝ)^4751 ≤ (1052065650257/10000000000000 : ℝ)^3727 := by
    have hnat : (854664067 : ℕ)^4751*10000000000000^3727 ≤ 1052065650257^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854664067 5000000000 1052065650257 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092011701/2000000000 : ℝ)^4751 ≤ (46237226712209/100000000000000 : ℝ)^3727 := by
    have hnat : (1092011701 : ℕ)^4751*100000000000000^3727 ≤ 46237226712209^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092011701 2000000000 46237226712209 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295153461/2500000000 : ℝ)^4751 ≤ (8648423353131/20000000000000 : ℝ)^3727 := by
    have hnat : (1295153461 : ℕ)^4751*20000000000000^3727 ≤ 8648423353131^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295153461 2500000000 8648423353131 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-854664067/5000000000 : ℝ), (1092011701/2000000000 : ℝ), (1295153461/2500000000 : ℝ)] ![(1052065650257/10000000000000 : ℝ), (46237226712209/100000000000000 : ℝ), (8648423353131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-854664067/5000000000 : ℝ)|^4751 ≤ (1052065650257/10000000000000 : ℝ)^3727
        have hw : |(-854664067/5000000000 : ℝ)|=(854664067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092011701/2000000000 : ℝ)|^4751 ≤ (46237226712209/100000000000000 : ℝ)^3727
        have hw : |(1092011701/2000000000 : ℝ)|=(1092011701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295153461/2500000000 : ℝ)|^4751 ≤ (8648423353131/20000000000000 : ℝ)^3727
        have hw : |(1295153461/2500000000 : ℝ)|=(1295153461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_1 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83653827/156250000 : ℝ)*x 0 + (-1853435543/10000000000 : ℝ)*x 1 + (5180613849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83653827/156250000 : ℝ)^4751 ≤ (5636717048347/12500000000000 : ℝ)^3727 := by
    have hnat : (83653827 : ℕ)^4751*12500000000000^3727 ≤ 5636717048347^3727*156250000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83653827 156250000 5636717048347 12500000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853435543/10000000000 : ℝ)^4751 ≤ (11664146776391/100000000000000 : ℝ)^3727 := by
    have hnat : (1853435543 : ℕ)^4751*100000000000000^3727 ≤ 11664146776391^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853435543 10000000000 11664146776391 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180613849/10000000000 : ℝ)^4751 ≤ (43242116818857/100000000000000 : ℝ)^3727 := by
    have hnat : (5180613849 : ℕ)^4751*100000000000000^3727 ≤ 43242116818857^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180613849 10000000000 43242116818857 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83653827/156250000 : ℝ), (-1853435543/10000000000 : ℝ), (5180613849/10000000000 : ℝ)] ![(5636717048347/12500000000000 : ℝ), (11664146776391/100000000000000 : ℝ), (43242116818857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83653827/156250000 : ℝ)|^4751 ≤ (5636717048347/12500000000000 : ℝ)^3727
        have hw : |(83653827/156250000 : ℝ)|=(83653827/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853435543/10000000000 : ℝ)|^4751 ≤ (11664146776391/100000000000000 : ℝ)^3727
        have hw : |(-1853435543/10000000000 : ℝ)|=(1853435543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180613849/10000000000 : ℝ)|^4751 ≤ (43242116818857/100000000000000 : ℝ)^3727
        have hw : |(5180613849/10000000000 : ℝ)|=(5180613849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_2 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353844891/10000000000 : ℝ)*x 0 + (5180613913/10000000000 : ℝ)*x 1 + (-1853435509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353844891/10000000000 : ℝ)^4751 ≤ (45093735989513/100000000000000 : ℝ)^3727 := by
    have hnat : (5353844891 : ℕ)^4751*100000000000000^3727 ≤ 45093735989513^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353844891 10000000000 45093735989513 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180613913/10000000000 : ℝ)^4751 ≤ (5405264687479/12500000000000 : ℝ)^3727 := by
    have hnat : (5180613913 : ℕ)^4751*12500000000000^3727 ≤ 5405264687479^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180613913 10000000000 5405264687479 12500000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1853435509/10000000000 : ℝ)^4751 ≤ (729009156477/6250000000000 : ℝ)^3727 := by
    have hnat : (1853435509 : ℕ)^4751*6250000000000^3727 ≤ 729009156477^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853435509 10000000000 729009156477 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353844891/10000000000 : ℝ), (5180613913/10000000000 : ℝ), (-1853435509/10000000000 : ℝ)] ![(45093735989513/100000000000000 : ℝ), (5405264687479/12500000000000 : ℝ), (729009156477/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353844891/10000000000 : ℝ)|^4751 ≤ (45093735989513/100000000000000 : ℝ)^3727
        have hw : |(5353844891/10000000000 : ℝ)|=(5353844891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180613913/10000000000 : ℝ)|^4751 ≤ (5405264687479/12500000000000 : ℝ)^3727
        have hw : |(5180613913/10000000000 : ℝ)|=(5180613913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1853435509/10000000000 : ℝ)|^4751 ≤ (729009156477/6250000000000 : ℝ)^3727
        have hw : |(-1853435509/10000000000 : ℝ)|=(1853435509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_3 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214197669/10000000000 : ℝ)*x 0 + (388250357/1000000000 : ℝ)*x 1 + (2283693149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214197669/10000000000 : ℝ)^4751 ≤ (33235685624581/100000000000000 : ℝ)^3727 := by
    have hnat : (4214197669 : ℕ)^4751*100000000000000^3727 ≤ 33235685624581^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214197669 10000000000 33235685624581 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388250357/1000000000 : ℝ)^4751 ≤ (14968890397101/50000000000000 : ℝ)^3727 := by
    have hnat : (388250357 : ℕ)^4751*50000000000000^3727 ≤ 14968890397101^3727*1000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388250357 1000000000 14968890397101 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283693149/5000000000 : ℝ)^4751 ≤ (1150829173847/3125000000000 : ℝ)^3727 := by
    have hnat : (2283693149 : ℕ)^4751*3125000000000^3727 ≤ 1150829173847^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283693149 5000000000 1150829173847 3125000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214197669/10000000000 : ℝ), (388250357/1000000000 : ℝ), (2283693149/5000000000 : ℝ)] ![(33235685624581/100000000000000 : ℝ), (14968890397101/50000000000000 : ℝ), (1150829173847/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214197669/10000000000 : ℝ)|^4751 ≤ (33235685624581/100000000000000 : ℝ)^3727
        have hw : |(4214197669/10000000000 : ℝ)|=(4214197669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388250357/1000000000 : ℝ)|^4751 ≤ (14968890397101/50000000000000 : ℝ)^3727
        have hw : |(388250357/1000000000 : ℝ)|=(388250357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2283693149/5000000000 : ℝ)|^4751 ≤ (1150829173847/3125000000000 : ℝ)^3727
        have hw : |(2283693149/5000000000 : ℝ)|=(2283693149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_4 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1709398721/10000000000 : ℝ)*x 0 + (2591344337/5000000000 : ℝ)*x 1 + (5457961883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1709398721/10000000000 : ℝ)^4751 ≤ (5260605162299/50000000000000 : ℝ)^3727 := by
    have hnat : (1709398721 : ℕ)^4751*50000000000000^3727 ≤ 5260605162299^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709398721 10000000000 5260605162299 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591344337/5000000000 : ℝ)^4751 ≤ (21632097333067/50000000000000 : ℝ)^3727 := by
    have hnat : (2591344337 : ℕ)^4751*50000000000000^3727 ≤ 21632097333067^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591344337 5000000000 21632097333067 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457961883/10000000000 : ℝ)^4751 ≤ (23107297501741/50000000000000 : ℝ)^3727 := by
    have hnat : (5457961883 : ℕ)^4751*50000000000000^3727 ≤ 23107297501741^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457961883 10000000000 23107297501741 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1709398721/10000000000 : ℝ), (2591344337/5000000000 : ℝ), (5457961883/10000000000 : ℝ)] ![(5260605162299/50000000000000 : ℝ), (21632097333067/50000000000000 : ℝ), (23107297501741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1709398721/10000000000 : ℝ)|^4751 ≤ (5260605162299/50000000000000 : ℝ)^3727
        have hw : |(-1709398721/10000000000 : ℝ)|=(1709398721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591344337/5000000000 : ℝ)|^4751 ≤ (21632097333067/50000000000000 : ℝ)^3727
        have hw : |(2591344337/5000000000 : ℝ)|=(2591344337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457961883/10000000000 : ℝ)|^4751 ≤ (23107297501741/50000000000000 : ℝ)^3727
        have hw : |(5457961883/10000000000 : ℝ)|=(5457961883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_5 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279658337/10000000000 : ℝ)*x 0 + (-1576087513/10000000000 : ℝ)*x 1 + (5457961883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279658337/10000000000 : ℝ)^4751 ≤ (11074682235899/25000000000000 : ℝ)^3727 := by
    have hnat : (5279658337 : ℕ)^4751*25000000000000^3727 ≤ 11074682235899^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279658337 10000000000 11074682235899 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1576087513/10000000000 : ℝ)^4751 ≤ (75893408321/800000000000 : ℝ)^3727 := by
    have hnat : (1576087513 : ℕ)^4751*800000000000^3727 ≤ 75893408321^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576087513 10000000000 75893408321 800000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457961883/10000000000 : ℝ)^4751 ≤ (23107297501741/50000000000000 : ℝ)^3727 := by
    have hnat : (5457961883 : ℕ)^4751*50000000000000^3727 ≤ 23107297501741^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457961883 10000000000 23107297501741 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279658337/10000000000 : ℝ), (-1576087513/10000000000 : ℝ), (5457961883/10000000000 : ℝ)] ![(11074682235899/25000000000000 : ℝ), (75893408321/800000000000 : ℝ), (23107297501741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279658337/10000000000 : ℝ)|^4751 ≤ (11074682235899/25000000000000 : ℝ)^3727
        have hw : |(5279658337/10000000000 : ℝ)|=(5279658337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1576087513/10000000000 : ℝ)|^4751 ≤ (75893408321/800000000000 : ℝ)^3727
        have hw : |(-1576087513/10000000000 : ℝ)|=(1576087513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457961883/10000000000 : ℝ)|^4751 ≤ (23107297501741/50000000000000 : ℝ)^3727
        have hw : |(5457961883/10000000000 : ℝ)|=(5457961883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_6 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639829169/5000000000 : ℝ)*x 0 + (5457961883/10000000000 : ℝ)*x 1 + (-1576087513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639829169/5000000000 : ℝ)^4751 ≤ (11074682238573/25000000000000 : ℝ)^3727 := by
    have hnat : (2639829169 : ℕ)^4751*25000000000000^3727 ≤ 11074682238573^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639829169 5000000000 11074682238573 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457961883/10000000000 : ℝ)^4751 ≤ (23107297501741/50000000000000 : ℝ)^3727 := by
    have hnat : (5457961883 : ℕ)^4751*50000000000000^3727 ≤ 23107297501741^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457961883 10000000000 23107297501741 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576087513/10000000000 : ℝ)^4751 ≤ (75893408321/800000000000 : ℝ)^3727 := by
    have hnat : (1576087513 : ℕ)^4751*800000000000^3727 ≤ 75893408321^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576087513 10000000000 75893408321 800000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639829169/5000000000 : ℝ), (5457961883/10000000000 : ℝ), (-1576087513/10000000000 : ℝ)] ![(11074682238573/25000000000000 : ℝ), (23107297501741/50000000000000 : ℝ), (75893408321/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639829169/5000000000 : ℝ)|^4751 ≤ (11074682238573/25000000000000 : ℝ)^3727
        have hw : |(2639829169/5000000000 : ℝ)|=(2639829169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457961883/10000000000 : ℝ)|^4751 ≤ (23107297501741/50000000000000 : ℝ)^3727
        have hw : |(5457961883/10000000000 : ℝ)|=(5457961883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576087513/10000000000 : ℝ)|^4751 ≤ (75893408321/800000000000 : ℝ)^3727
        have hw : |(-1576087513/10000000000 : ℝ)|=(1576087513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s4_7 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (842874133/2000000000 : ℝ)*x 0 + (4562301207/10000000000 : ℝ)*x 1 + (3887642099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842874133/2000000000 : ℝ)^4751 ≤ (16618712421023/50000000000000 : ℝ)^3727 := by
    have hnat : (842874133 : ℕ)^4751*50000000000000^3727 ≤ 16618712421023^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842874133 2000000000 16618712421023 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562301207/10000000000 : ℝ)^4751 ≤ (36774275775877/100000000000000 : ℝ)^3727 := by
    have hnat : (4562301207 : ℕ)^4751*100000000000000^3727 ≤ 36774275775877^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562301207 10000000000 36774275775877 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3887642099/10000000000 : ℝ)^4751 ≤ (29988299372513/100000000000000 : ℝ)^3727 := by
    have hnat : (3887642099 : ℕ)^4751*100000000000000^3727 ≤ 29988299372513^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3887642099 10000000000 29988299372513 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842874133/2000000000 : ℝ), (4562301207/10000000000 : ℝ), (3887642099/10000000000 : ℝ)] ![(16618712421023/50000000000000 : ℝ), (36774275775877/100000000000000 : ℝ), (29988299372513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842874133/2000000000 : ℝ)|^4751 ≤ (16618712421023/50000000000000 : ℝ)^3727
        have hw : |(842874133/2000000000 : ℝ)|=(842874133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562301207/10000000000 : ℝ)|^4751 ≤ (36774275775877/100000000000000 : ℝ)^3727
        have hw : |(4562301207/10000000000 : ℝ)|=(4562301207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3887642099/10000000000 : ℝ)|^4751 ≤ (29988299372513/100000000000000 : ℝ)^3727
        have hw : |(3887642099/10000000000 : ℝ)|=(3887642099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1608_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1041/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10421/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3269/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1041/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8179/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1041/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1041/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8179/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1041/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1041/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8179/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1041/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1041/10000 : ℝ) ^ (4747/1024 : ℝ) ≤ (1393557521995849/50000000000000000000 : ℝ) := by
    have hpowers : (1041/10000 : ℝ)^4747 ≤ (1393557521995849/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1041 : ℕ)^4747*50000000000000000000^1024 ≤ 1393557521995849^1024*10000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1041 10000 1393557521995849 50000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1041/10000 : ℝ)) (X := (1393557521995849/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8179/50000 : ℝ) ^ (4747/1024 : ℝ) ≤ (22649360027794323/100000000000000000000 : ℝ) := by
    have hpowers : (8179/50000 : ℝ)^4747 ≤ (22649360027794323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8179 : ℕ)^4747*100000000000000000000^1024 ≤ 22649360027794323^1024*50000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8179 50000 22649360027794323 100000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8179/50000 : ℝ)) (X := (22649360027794323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001393557521995849/25000000000000000000 : ℝ) ≤ (1000012024198111/1000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (25001393557521995849/25000000000000000000 : ℝ)^1024 ≤ (1000012024198111/1000000000000000 : ℝ)^4747 := by
      have hnat : (25001393557521995849 : ℕ)^1024*1000000000000000^4747 ≤ 1000012024198111^4747*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001393557521995849 25000000000000000000 1000012024198111 1000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000012024198111/1000000000000000 : ℝ)) (X := (25001393557521995849/25000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025436475071786021/100000000000000000000 : ℝ) ≤ (10000548648678239/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (100025436475071786021/100000000000000000000 : ℝ)^1024 ≤ (10000548648678239/10000000000000000 : ℝ)^4747 := by
      have hnat : (100025436475071786021 : ℕ)^1024*10000000000000000^4747 ≤ 10000548648678239^4747*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025436475071786021 100000000000000000000 10000548648678239 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000548648678239/10000000000000000 : ℝ)) (X := (100025436475071786021/100000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022649360027794323/50000000000000000000 : ℝ) ≤ (1250122131921921/1250000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (50022649360027794323/50000000000000000000 : ℝ)^1024 ≤ (1250122131921921/1250000000000000 : ℝ)^4747 := by
      have hnat : (50022649360027794323 : ℕ)^1024*1250000000000000^4747 ≤ 1250122131921921^4747*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022649360027794323 50000000000000000000 1250122131921921 1250000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250122131921921/1250000000000000 : ℝ)) (X := (50022649360027794323/50000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1393557521995849/50000000000000000000 : ℝ) ≤ ((118943591543738833/118960000000000000 : ℝ)+2*(428406697129/594800000000000 : ℝ)*(1041/10000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (118943591543738833/118960000000000000 : ℝ)+2*(428406697129/594800000000000 : ℝ)*(1041/10000 : ℝ)=(1000012024198111/1000000000000000 : ℝ) by norm_num, show 1+2*(1393557521995849/50000000000000000000 : ℝ)=(25001393557521995849/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22649360027794323/100000000000000000000 : ℝ)+(1393557521995849/50000000000000000000 : ℝ) ≤ ((118943591543738833/118960000000000000 : ℝ)+(428406697129/594800000000000 : ℝ)*((8179/50000 : ℝ)+(1041/10000 : ℝ)))^(4747/1024 : ℝ) := by
    rw [show (118943591543738833/118960000000000000 : ℝ)+(428406697129/594800000000000 : ℝ)*((8179/50000 : ℝ)+(1041/10000 : ℝ))=(10000548648678239/10000000000000000 : ℝ) by norm_num, show 1+(22649360027794323/100000000000000000000 : ℝ)+(1393557521995849/50000000000000000000 : ℝ)=(100025436475071786021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22649360027794323/100000000000000000000 : ℝ) ≤ ((118943591543738833/118960000000000000 : ℝ)+2*(428406697129/594800000000000 : ℝ)*(8179/50000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (118943591543738833/118960000000000000 : ℝ)+2*(428406697129/594800000000000 : ℝ)*(8179/50000 : ℝ)=(1250122131921921/1250000000000000 : ℝ) by norm_num, show 1+2*(22649360027794323/100000000000000000000 : ℝ)=(50022649360027794323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (118943591543738833/118960000000000000 : ℝ)*(X 1 0+X 2 0)+(428406697129/594800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (1041/10000 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (118943591543738833/118960000000000000 : ℝ)) (alpha := (428406697129/594800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (118943591543738833/118960000000000000 : ℝ)*(X 0 1+X 2 1)+(428406697129/594800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (1041/10000 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (118943591543738833/118960000000000000 : ℝ)) (alpha := (428406697129/594800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (118943591543738833/118960000000000000 : ℝ)*(X 0 2+X 1 2)+(428406697129/594800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (1041/10000 : ℝ)) (hi := (8179/50000 : ℝ)) (c := (118943591543738833/118960000000000000 : ℝ)) (alpha := (428406697129/594800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-854664067/5000000000 : ℝ)*X 0 0+(1092011701/2000000000 : ℝ)*X 0 1+(1295153461/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83653827/156250000 : ℝ)*X 1 0+(-1853435543/10000000000 : ℝ)*X 1 1+(5180613849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353844891/10000000000 : ℝ)*X 2 0+(5180613913/10000000000 : ℝ)*X 2 1+(-1853435509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4214197669/10000000000 : ℝ)*X 0 0+(388250357/1000000000 : ℝ)*X 0 1+(2283693149/5000000000 : ℝ)*X 0 2+(4214197669/10000000000 : ℝ)*X 1 0+(388250357/1000000000 : ℝ)*X 1 1+(2283693149/5000000000 : ℝ)*X 1 2+(4214197669/10000000000 : ℝ)*X 2 0+(388250357/1000000000 : ℝ)*X 2 1+(2283693149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1709398721/10000000000 : ℝ)*X 0 0+(2591344337/5000000000 : ℝ)*X 0 1+(5457961883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279658337/10000000000 : ℝ)*X 1 0+(-1576087513/10000000000 : ℝ)*X 1 1+(5457961883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639829169/5000000000 : ℝ)*X 2 0+(5457961883/10000000000 : ℝ)*X 2 1+(-1576087513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842874133/2000000000 : ℝ)*X 0 0+(4562301207/10000000000 : ℝ)*X 0 1+(3887642099/10000000000 : ℝ)*X 0 2+(842874133/2000000000 : ℝ)*X 1 0+(4562301207/10000000000 : ℝ)*X 1 1+(3887642099/10000000000 : ℝ)*X 1 2+(842874133/2000000000 : ℝ)*X 2 0+(4562301207/10000000000 : ℝ)*X 2 1+(3887642099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30763032596436366821795937/2974000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85914939/5000000000000 : ℝ)*(base19) + (1582202403/100000000000000 : ℝ)*(base23) + (59623193/100000000000000 : ℝ)*(lower2) + (30972227/12500000000000 : ℝ)*(upper3) + (188551641/100000000000000 : ℝ)*(upper5) + (1259672467600521/50000000000000 : ℝ)*(major0) + (1259672467600521/50000000000000 : ℝ)*(major1) + (1259672467600521/50000000000000 : ℝ)*(major2) + (71570946427953/2000000000000 : ℝ)*(sp0) + (223660412006637/6250000000000 : ℝ)*(sp1) + (447320841025321/12500000000000 : ℝ)*(sp2) + (1460112195421823/100000000000000 : ℝ)*(sp3) + (10494503661/50000000000000 : ℝ)*(sp4) + (1803955109/20000000000000 : ℝ)*(sp7) + (182515151899671/12500000000000 : ℝ)*(f.failure) + (3578568310404971/100000000000000 : ℝ)*(f.sum) + (30285957061709/14870000000000000000000000000 : ℝ)*base65 + (21286055587870207/5948000000000000000000000000000 : ℝ)*base68 + (31695346635406207/5948000000000000000000000000000 : ℝ)*base70 + (46203042374650207/5948000000000000000000000000000 : ℝ)*base72 + (93706344696179/14870000000000000000000000000 : ℝ)*base73 + (54600375415142207/5948000000000000000000000000000 : ℝ)*base76 + (7084746979226207/5948000000000000000000000000000 : ℝ)*base78 + (19270541919958207/5948000000000000000000000000000 : ℝ)*base80 + (65393055351819/14870000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2526963/1250000000000000000000 : ℝ)*base90 + (2526963/1250000000000000000000 : ℝ)*base92 + (2526963/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15833423413076765389023/3717500000000000000000000000 : ℝ) := by norm_num
    linear_combination (326902911/50000000000000 : ℝ)*(base19) + (141774091/20000000000000 : ℝ)*(base23) + (5189047/2500000000000 : ℝ)*(lower1) + (22349803/25000000000000 : ℝ)*(upper3) + (24419043/100000000000000 : ℝ)*(lower4) + (44144347/50000000000000 : ℝ)*(upper5) + (639371706530703/25000000000000 : ℝ)*(major0) + (639371706530703/25000000000000 : ℝ)*(major1) + (639371706530703/25000000000000 : ℝ)*(major2) + (578264093/100000000000000 : ℝ)*(sp2) + (56761666163377/1562500000000 : ℝ)*(sp4) + (726549196130061/20000000000000 : ℝ)*(sp5) + (181637267366079/5000000000000 : ℝ)*(sp6) + (1482226875817507/100000000000000 : ℝ)*(sp7) + (1482226875817507/100000000000000 : ℝ)*(f.failure) + (56761666163377/1562500000000 : ℝ)*(f.sum) + (9786880629729/3717500000000000000000000000 : ℝ)*base66 + (17134949210972999/2974000000000000000000000000000 : ℝ)*base67 + (16733768731131001/2974000000000000000000000000000 : ℝ)*base70 + (442698439146666999/2974000000000000000000000000000 : ℝ)*base71 + (7881689138147/7435000000000000000000000000 : ℝ)*base73 + (133262688166565001/2974000000000000000000000000000 : ℝ)*base76 + (10230727664265001/2974000000000000000000000000000 : ℝ)*base78 + (9307480016174999/2974000000000000000000000000000 : ℝ)*base79 + (33066044227773/7435000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17522671/10000000000000000000000 : ℝ)*base90 + (17522671/10000000000000000000000 : ℝ)*base92 + (17522671/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1608_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8179/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1041/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10421/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1608_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1608_s5_0 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53416863/312500000 : ℝ)*x 0 + (2730002877/5000000000 : ℝ)*x 1 + (323791181/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53416863/312500000 : ℝ)^4751 ≤ (10520746589333/100000000000000 : ℝ)^3727 := by
    have hnat : (53416863 : ℕ)^4751*100000000000000^3727 ≤ 10520746589333^3727*312500000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53416863 312500000 10520746589333 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730002877/5000000000 : ℝ)^4751 ≤ (23118328634617/50000000000000 : ℝ)^3727 := by
    have hnat : (2730002877 : ℕ)^4751*50000000000000^3727 ≤ 23118328634617^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730002877 5000000000 23118328634617 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323791181/625000000 : ℝ)^4751 ≤ (43242596130251/100000000000000 : ℝ)^3727 := by
    have hnat : (323791181 : ℕ)^4751*100000000000000^3727 ≤ 43242596130251^3727*625000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323791181 625000000 43242596130251 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53416863/312500000 : ℝ), (2730002877/5000000000 : ℝ), (323791181/625000000 : ℝ)] ![(10520746589333/100000000000000 : ℝ), (23118328634617/50000000000000 : ℝ), (43242596130251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53416863/312500000 : ℝ)|^4751 ≤ (10520746589333/100000000000000 : ℝ)^3727
        have hw : |(-53416863/312500000 : ℝ)|=(53416863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730002877/5000000000 : ℝ)|^4751 ≤ (23118328634617/50000000000000 : ℝ)^3727
        have hw : |(2730002877/5000000000 : ℝ)|=(2730002877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323791181/625000000 : ℝ)|^4751 ≤ (43242596130251/100000000000000 : ℝ)^3727
        have hw : |(323791181/625000000 : ℝ)|=(323791181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_1 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353830513/10000000000 : ℝ)*x 0 + (-1853394917/10000000000 : ℝ)*x 1 + (207226361/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353830513/10000000000 : ℝ)^4751 ≤ (4509358161543/10000000000000 : ℝ)^3727 := by
    have hnat : (5353830513 : ℕ)^4751*10000000000000^3727 ≤ 4509358161543^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353830513 10000000000 4509358161543 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1853394917/10000000000 : ℝ)^4751 ≤ (11663820861741/100000000000000 : ℝ)^3727 := by
    have hnat : (1853394917 : ℕ)^4751*100000000000000^3727 ≤ 11663820861741^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853394917 10000000000 11663820861741 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207226361/400000000 : ℝ)^4751 ≤ (8648519500569/20000000000000 : ℝ)^3727 := by
    have hnat : (207226361 : ℕ)^4751*20000000000000^3727 ≤ 8648519500569^3727*400000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207226361 400000000 8648519500569 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353830513/10000000000 : ℝ), (-1853394917/10000000000 : ℝ), (207226361/400000000 : ℝ)] ![(4509358161543/10000000000000 : ℝ), (11663820861741/100000000000000 : ℝ), (8648519500569/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353830513/10000000000 : ℝ)|^4751 ≤ (4509358161543/10000000000000 : ℝ)^3727
        have hw : |(5353830513/10000000000 : ℝ)|=(5353830513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1853394917/10000000000 : ℝ)|^4751 ≤ (11663820861741/100000000000000 : ℝ)^3727
        have hw : |(-1853394917/10000000000 : ℝ)|=(1853394917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207226361/400000000 : ℝ)|^4751 ≤ (8648519500569/20000000000000 : ℝ)^3727
        have hw : |(207226361/400000000 : ℝ)|=(207226361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_2 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353830493/10000000000 : ℝ)*x 0 + (5180659009/10000000000 : ℝ)*x 1 + (-926697483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353830493/10000000000 : ℝ)^4751 ≤ (22546790700347/50000000000000 : ℝ)^3727 := by
    have hnat : (5353830493 : ℕ)^4751*50000000000000^3727 ≤ 22546790700347^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353830493 10000000000 22546790700347 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180659009/10000000000 : ℝ)^4751 ≤ (43242597332601/100000000000000 : ℝ)^3727 := by
    have hnat : (5180659009 : ℕ)^4751*100000000000000^3727 ≤ 43242597332601^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180659009 10000000000 43242597332601 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926697483/5000000000 : ℝ)^4751 ≤ (11663821254833/100000000000000 : ℝ)^3727 := by
    have hnat : (926697483 : ℕ)^4751*100000000000000^3727 ≤ 11663821254833^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926697483 5000000000 11663821254833 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353830493/10000000000 : ℝ), (5180659009/10000000000 : ℝ), (-926697483/5000000000 : ℝ)] ![(22546790700347/50000000000000 : ℝ), (43242597332601/100000000000000 : ℝ), (11663821254833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353830493/10000000000 : ℝ)|^4751 ≤ (22546790700347/50000000000000 : ℝ)^3727
        have hw : |(5353830493/10000000000 : ℝ)|=(5353830493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180659009/10000000000 : ℝ)|^4751 ≤ (43242597332601/100000000000000 : ℝ)^3727
        have hw : |(5180659009/10000000000 : ℝ)|=(5180659009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-926697483/5000000000 : ℝ)|^4751 ≤ (11663821254833/100000000000000 : ℝ)^3727
        have hw : |(-926697483/5000000000 : ℝ)|=(926697483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_3 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214204419/10000000000 : ℝ)*x 0 + (155304909/400000000 : ℝ)*x 1 + (2283632871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214204419/10000000000 : ℝ)^4751 ≤ (33235753485423/100000000000000 : ℝ)^3727 := by
    have hnat : (4214204419 : ℕ)^4751*100000000000000^3727 ≤ 33235753485423^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214204419 10000000000 33235753485423 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155304909/400000000 : ℝ)^4751 ≤ (14969476019237/50000000000000 : ℝ)^3727 := by
    have hnat : (155304909 : ℕ)^4751*50000000000000^3727 ≤ 14969476019237^3727*400000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155304909 400000000 14969476019237 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283632871/5000000000 : ℝ)^4751 ≤ (36825294464153/100000000000000 : ℝ)^3727 := by
    have hnat : (2283632871 : ℕ)^4751*100000000000000^3727 ≤ 36825294464153^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283632871 5000000000 36825294464153 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214204419/10000000000 : ℝ), (155304909/400000000 : ℝ), (2283632871/5000000000 : ℝ)] ![(33235753485423/100000000000000 : ℝ), (14969476019237/50000000000000 : ℝ), (36825294464153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214204419/10000000000 : ℝ)|^4751 ≤ (33235753485423/100000000000000 : ℝ)^3727
        have hw : |(4214204419/10000000000 : ℝ)|=(4214204419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(155304909/400000000 : ℝ)|^4751 ≤ (14969476019237/50000000000000 : ℝ)^3727
        have hw : |(155304909/400000000 : ℝ)|=(155304909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2283632871/5000000000 : ℝ)|^4751 ≤ (36825294464153/100000000000000 : ℝ)^3727
        have hw : |(2283632871/5000000000 : ℝ)|=(2283632871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_4 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-341882001/2000000000 : ℝ)*x 0 + (161960387/312500000 : ℝ)*x 1 + (5457910587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341882001/2000000000 : ℝ)^4751 ≤ (5260649429437/50000000000000 : ℝ)^3727 := by
    have hnat : (341882001 : ℕ)^4751*50000000000000^3727 ≤ 5260649429437^3727*2000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341882001 2000000000 5260649429437 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161960387/312500000 : ℝ)^4751 ≤ (21632329901333/50000000000000 : ℝ)^3727 := by
    have hnat : (161960387 : ℕ)^4751*50000000000000^3727 ≤ 21632329901333^3727*312500000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161960387 312500000 21632329901333 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5457910587/10000000000 : ℝ)^4751 ≤ (46214041325529/100000000000000 : ℝ)^3727 := by
    have hnat : (5457910587 : ℕ)^4751*100000000000000^3727 ≤ 46214041325529^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457910587 10000000000 46214041325529 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-341882001/2000000000 : ℝ), (161960387/312500000 : ℝ), (5457910587/10000000000 : ℝ)] ![(5260649429437/50000000000000 : ℝ), (21632329901333/50000000000000 : ℝ), (46214041325529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-341882001/2000000000 : ℝ)|^4751 ≤ (5260649429437/50000000000000 : ℝ)^3727
        have hw : |(-341882001/2000000000 : ℝ)|=(341882001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161960387/312500000 : ℝ)|^4751 ≤ (21632329901333/50000000000000 : ℝ)^3727
        have hw : |(161960387/312500000 : ℝ)|=(161960387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5457910587/10000000000 : ℝ)|^4751 ≤ (46214041325529/100000000000000 : ℝ)^3727
        have hw : |(5457910587/10000000000 : ℝ)|=(5457910587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_5 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164989687/312500000 : ℝ)*x 0 + (-157614329/1000000000 : ℝ)*x 1 + (1364477673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164989687/312500000 : ℝ)^4751 ≤ (11074713379247/25000000000000 : ℝ)^3727 := by
    have hnat : (164989687 : ℕ)^4751*25000000000000^3727 ≤ 11074713379247^3727*312500000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164989687 312500000 11074713379247 25000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157614329/1000000000 : ℝ)^4751 ≤ (592944000837/6250000000000 : ℝ)^3727 := by
    have hnat : (157614329 : ℕ)^4751*6250000000000^3727 ≤ 592944000837^3727*1000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157614329 1000000000 592944000837 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364477673/2500000000 : ℝ)^4751 ≤ (23107021229437/50000000000000 : ℝ)^3727 := by
    have hnat : (1364477673 : ℕ)^4751*50000000000000^3727 ≤ 23107021229437^3727*2500000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364477673 2500000000 23107021229437 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164989687/312500000 : ℝ), (-157614329/1000000000 : ℝ), (1364477673/2500000000 : ℝ)] ![(11074713379247/25000000000000 : ℝ), (592944000837/6250000000000 : ℝ), (23107021229437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164989687/312500000 : ℝ)|^4751 ≤ (11074713379247/25000000000000 : ℝ)^3727
        have hw : |(164989687/312500000 : ℝ)|=(164989687/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-157614329/1000000000 : ℝ)|^4751 ≤ (592944000837/6250000000000 : ℝ)^3727
        have hw : |(-157614329/1000000000 : ℝ)|=(157614329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364477673/2500000000 : ℝ)|^4751 ≤ (23107021229437/50000000000000 : ℝ)^3727
        have hw : |(1364477673/2500000000 : ℝ)|=(1364477673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_6 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (329979377/625000000 : ℝ)*x 0 + (5457910621/10000000000 : ℝ)*x 1 + (-1576143321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329979377/625000000 : ℝ)^4751 ≤ (2768678376899/6250000000000 : ℝ)^3727 := by
    have hnat : (329979377 : ℕ)^4751*6250000000000^3727 ≤ 2768678376899^3727*625000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329979377 625000000 2768678376899 6250000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457910621/10000000000 : ℝ)^4751 ≤ (46214041692517/100000000000000 : ℝ)^3727 := by
    have hnat : (5457910621 : ℕ)^4751*100000000000000^3727 ≤ 46214041692517^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457910621 10000000000 46214041692517 100000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576143321/10000000000 : ℝ)^4751 ≤ (1897420850251/20000000000000 : ℝ)^3727 := by
    have hnat : (1576143321 : ℕ)^4751*20000000000000^3727 ≤ 1897420850251^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576143321 10000000000 1897420850251 20000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329979377/625000000 : ℝ), (5457910621/10000000000 : ℝ), (-1576143321/10000000000 : ℝ)] ![(2768678376899/6250000000000 : ℝ), (46214041692517/100000000000000 : ℝ), (1897420850251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329979377/625000000 : ℝ)|^4751 ≤ (2768678376899/6250000000000 : ℝ)^3727
        have hw : |(329979377/625000000 : ℝ)|=(329979377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457910621/10000000000 : ℝ)|^4751 ≤ (46214041692517/100000000000000 : ℝ)^3727
        have hw : |(5457910621/10000000000 : ℝ)|=(5457910621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576143321/10000000000 : ℝ)|^4751 ≤ (1897420850251/20000000000000 : ℝ)^3727
        have hw : |(-1576143321/10000000000 : ℝ)|=(1576143321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1608_s5_7 (p : ℝ) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4214377321/10000000000 : ℝ)*x 0 + (4562184159/10000000000 : ℝ)*x 1 + (1943878801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4214377321/10000000000 : ℝ)^4751 ≤ (16618745879309/50000000000000 : ℝ)^3727 := by
    have hnat : (4214377321 : ℕ)^4751*50000000000000^3727 ≤ 16618745879309^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214377321 10000000000 16618745879309 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562184159/10000000000 : ℝ)^4751 ≤ (3677307310089/10000000000000 : ℝ)^3727 := by
    have hnat : (4562184159 : ℕ)^4751*10000000000000^3727 ≤ 3677307310089^3727*10000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562184159 10000000000 3677307310089 10000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1943878801/5000000000 : ℝ)^4751 ≤ (14994717565821/50000000000000 : ℝ)^3727 := by
    have hnat : (1943878801 : ℕ)^4751*50000000000000^3727 ≤ 14994717565821^3727*5000000000^4751 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943878801 5000000000 14994717565821 50000000000000 4751 3727 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4751/1024 : ℝ)) 4751 3727 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4214377321/10000000000 : ℝ), (4562184159/10000000000 : ℝ), (1943878801/5000000000 : ℝ)] ![(16618745879309/50000000000000 : ℝ), (3677307310089/10000000000000 : ℝ), (14994717565821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4214377321/10000000000 : ℝ)|^4751 ≤ (16618745879309/50000000000000 : ℝ)^3727
        have hw : |(4214377321/10000000000 : ℝ)|=(4214377321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562184159/10000000000 : ℝ)|^4751 ≤ (3677307310089/10000000000000 : ℝ)^3727
        have hw : |(4562184159/10000000000 : ℝ)|=(4562184159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1943878801/5000000000 : ℝ)|^4751 ≤ (14994717565821/50000000000000 : ℝ)^3727
        have hw : |(1943878801/5000000000 : ℝ)|=(1943878801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1608_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5211/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2043/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3269/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3269/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10421/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3269/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3269/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10421/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3269/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3269/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10421/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10421/100000 : ℝ) ^ (4747/1024 : ℝ) ≤ (280079391758193/10000000000000000000 : ℝ) := by
    have hpowers : (10421/100000 : ℝ)^4747 ≤ (280079391758193/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10421 : ℕ)^4747*10000000000000000000^1024 ≤ 280079391758193^1024*100000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10421 100000 280079391758193 10000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10421/100000 : ℝ)) (X := (280079391758193/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3269/20000 : ℝ) ^ (4747/1024 : ℝ) ≤ (22566037790917323/100000000000000000000 : ℝ) := by
    have hpowers : (3269/20000 : ℝ)^4747 ≤ (22566037790917323/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3269 : ℕ)^4747*100000000000000000000^1024 ≤ 22566037790917323^1024*20000^4747 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3269 20000 22566037790917323 100000000000000000000 4747 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3269/20000 : ℝ)) (X := (22566037790917323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000280079391758193/5000000000000000000 : ℝ) ≤ (10000120832103407/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (5000280079391758193/5000000000000000000 : ℝ)^1024 ≤ (10000120832103407/10000000000000000 : ℝ)^4747 := by
      have hnat : (5000280079391758193 : ℕ)^1024*10000000000000000^4747 ≤ 10000120832103407^4747*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000280079391758193 5000000000000000000 10000120832103407 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000120832103407/10000000000000000 : ℝ)) (X := (5000280079391758193/5000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025366831708499253/100000000000000000000 : ℝ) ≤ (500027357333217/500000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (100025366831708499253/100000000000000000000 : ℝ)^1024 ≤ (500027357333217/500000000000000 : ℝ)^4747 := by
      have hnat : (100025366831708499253 : ℕ)^1024*500000000000000^4747 ≤ 500027357333217^4747*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025366831708499253 100000000000000000000 500027357333217 500000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500027357333217/500000000000000 : ℝ)) (X := (100025366831708499253/100000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022566037790917323/50000000000000000000 : ℝ) ≤ (10000973461225273/10000000000000000 : ℝ) ^ (4747/1024 : ℝ) := by
    have hpowers : (50022566037790917323/50000000000000000000 : ℝ)^1024 ≤ (10000973461225273/10000000000000000 : ℝ)^4747 := by
      have hnat : (50022566037790917323 : ℕ)^1024*10000000000000000^4747 ≤ 10000973461225273^4747*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022566037790917323 50000000000000000000 10000973461225273 10000000000000000 1024 4747 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000973461225273/10000000000000000 : ℝ)) (X := (50022566037790917323/50000000000000000000 : ℝ)) (by norm_num) 4747 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(280079391758193/10000000000000000000 : ℝ) ≤ ((29615915280650808741/29620000000000000000 : ℝ)+2*(426314560933/592400000000000 : ℝ)*(10421/100000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (29615915280650808741/29620000000000000000 : ℝ)+2*(426314560933/592400000000000 : ℝ)*(10421/100000 : ℝ)=(10000120832103407/10000000000000000 : ℝ) by norm_num, show 1+2*(280079391758193/10000000000000000000 : ℝ)=(5000280079391758193/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22566037790917323/100000000000000000000 : ℝ)+(280079391758193/10000000000000000000 : ℝ) ≤ ((29615915280650808741/29620000000000000000 : ℝ)+(426314560933/592400000000000 : ℝ)*((3269/20000 : ℝ)+(10421/100000 : ℝ)))^(4747/1024 : ℝ) := by
    rw [show (29615915280650808741/29620000000000000000 : ℝ)+(426314560933/592400000000000 : ℝ)*((3269/20000 : ℝ)+(10421/100000 : ℝ))=(500027357333217/500000000000000 : ℝ) by norm_num, show 1+(22566037790917323/100000000000000000000 : ℝ)+(280079391758193/10000000000000000000 : ℝ)=(100025366831708499253/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22566037790917323/100000000000000000000 : ℝ) ≤ ((29615915280650808741/29620000000000000000 : ℝ)+2*(426314560933/592400000000000 : ℝ)*(3269/20000 : ℝ))^(4747/1024 : ℝ) := by
    rw [show (29615915280650808741/29620000000000000000 : ℝ)+2*(426314560933/592400000000000 : ℝ)*(3269/20000 : ℝ)=(10000973461225273/10000000000000000 : ℝ) by norm_num, show 1+2*(22566037790917323/100000000000000000000 : ℝ)=(50022566037790917323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29615915280650808741/29620000000000000000 : ℝ)*(X 1 0+X 2 0)+(426314560933/592400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (10421/100000 : ℝ)) (hi := (3269/20000 : ℝ)) (c := (29615915280650808741/29620000000000000000 : ℝ)) (alpha := (426314560933/592400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29615915280650808741/29620000000000000000 : ℝ)*(X 0 1+X 2 1)+(426314560933/592400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (10421/100000 : ℝ)) (hi := (3269/20000 : ℝ)) (c := (29615915280650808741/29620000000000000000 : ℝ)) (alpha := (426314560933/592400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29615915280650808741/29620000000000000000 : ℝ)*(X 0 2+X 1 2)+(426314560933/592400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4747/1024 : ℝ)) (lo := (10421/100000 : ℝ)) (hi := (3269/20000 : ℝ)) (c := (29615915280650808741/29620000000000000000 : ℝ)) (alpha := (426314560933/592400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53416863/312500000 : ℝ)*X 0 0+(2730002877/5000000000 : ℝ)*X 0 1+(323791181/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353830513/10000000000 : ℝ)*X 1 0+(-1853394917/10000000000 : ℝ)*X 1 1+(207226361/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353830493/10000000000 : ℝ)*X 2 0+(5180659009/10000000000 : ℝ)*X 2 1+(-926697483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4214204419/10000000000 : ℝ)*X 0 0+(155304909/400000000 : ℝ)*X 0 1+(2283632871/5000000000 : ℝ)*X 0 2+(4214204419/10000000000 : ℝ)*X 1 0+(155304909/400000000 : ℝ)*X 1 1+(2283632871/5000000000 : ℝ)*X 1 2+(4214204419/10000000000 : ℝ)*X 2 0+(155304909/400000000 : ℝ)*X 2 1+(2283632871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-341882001/2000000000 : ℝ)*X 0 0+(161960387/312500000 : ℝ)*X 0 1+(5457910587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164989687/312500000 : ℝ)*X 1 0+(-157614329/1000000000 : ℝ)*X 1 1+(1364477673/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((329979377/625000000 : ℝ)*X 2 0+(5457910621/10000000000 : ℝ)*X 2 1+(-1576143321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4214377321/10000000000 : ℝ)*X 0 0+(4562184159/10000000000 : ℝ)*X 0 1+(1943878801/5000000000 : ℝ)*X 0 2+(4214377321/10000000000 : ℝ)*X 1 0+(4562184159/10000000000 : ℝ)*X 1 1+(1943878801/5000000000 : ℝ)*X 1 2+(4214377321/10000000000 : ℝ)*X 2 0+(4562184159/10000000000 : ℝ)*X 2 1+(1943878801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1608_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14879462615833017895820044749/1481000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81786623/5000000000000 : ℝ)*(base19) + (19658437/1250000000000 : ℝ)*(base23) + (26600277/100000000000000 : ℝ)*(lower2) + (128951027/50000000000000 : ℝ)*(upper3) + (91551339/50000000000000 : ℝ)*(upper5) + (2520227263004963/100000000000000 : ℝ)*(major0) + (2520227263004963/100000000000000 : ℝ)*(major1) + (2520227263004963/100000000000000 : ℝ)*(major2) + (1789900406948901/50000000000000 : ℝ)*(sp0) + (894954993724143/25000000000000 : ℝ)*(sp1) + (447477504744259/12500000000000 : ℝ)*(sp2) + (1460623491660781/100000000000000 : ℝ)*(sp3) + (20796731229/100000000000000 : ℝ)*(sp4) + (4544411679/50000000000000 : ℝ)*(sp7) + (1460632580484139/100000000000000 : ℝ)*(f.failure) + (447477701328629/12500000000000 : ℝ)*(f.sum) + (40638950197121/29620000000000000000000000000 : ℝ)*base66 + (5007205493571268417/2962000000000000000000000000000000 : ℝ)*base68 + (17249282523624731583/2962000000000000000000000000000000 : ℝ)*base69 + (2561925807095268417/2962000000000000000000000000000000 : ℝ)*base72 + (129087962122781/29620000000000000000000000000 : ℝ)*base74 + (45114425748545268417/2962000000000000000000000000000000 : ℝ)*base76 + (6873773823184731583/2962000000000000000000000000000000 : ℝ)*base77 + (8160734349419268417/2962000000000000000000000000000000 : ℝ)*base80 + (16381164507559/29620000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (20301033/10000000000000000000000 : ℝ)*base89 + (20301033/10000000000000000000000 : ℝ)*base91 + (20301033/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81569156842187829923049/14810000000000000000000000000 : ℝ) := by norm_num
    linear_combination (711715367/100000000000000 : ℝ)*(base19) + (10957147/1250000000000 : ℝ)*(base23) + (2935313/1250000000000 : ℝ)*(lower1) + (25319887/20000000000000 : ℝ)*(upper3) + (577411/1000000000000 : ℝ)*(lower4) + (22428187/25000000000000 : ℝ)*(upper5) + (1279184164728569/50000000000000 : ℝ)*(major0) + (1279184164728569/50000000000000 : ℝ)*(major1) + (1279184164728569/50000000000000 : ℝ)*(major2) + (799242759/50000000000000 : ℝ)*(sp2) + (227124919503279/6250000000000 : ℝ)*(sp4) + (1816999000168549/50000000000000 : ℝ)*(sp5) + (908499059248797/25000000000000 : ℝ)*(sp6) + (370684440817879/25000000000000 : ℝ)*(sp7) + (370684440817879/25000000000000 : ℝ)*(f.failure) + (227124919503279/6250000000000 : ℝ)*(f.sum) + (8072907054917/14810000000000000000000000000 : ℝ)*base65 + (13538222778478528371/1481000000000000000000000000000000 : ℝ)*base68 + (12964728695341471629/1481000000000000000000000000000000 : ℝ)*base69 + (34403359179366528371/1481000000000000000000000000000000 : ℝ)*base72 + (10869682133437/14810000000000000000000000000 : ℝ)*base73 + (192145860416853471629/1481000000000000000000000000000000 : ℝ)*base75 + (3352010842835471629/1481000000000000000000000000000000 : ℝ)*base77 + (3192000074032528371/1481000000000000000000000000000000 : ℝ)*base80 + (51306848694883/14810000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (26323187/2500000000000000000000 : ℝ)*base90 + (26323187/2500000000000000000000 : ℝ)*base92 + (26323187/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1608_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3269/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10421/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5211/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1608_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1608_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5211/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1608_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1608_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1608_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4747/1024 : ℝ) ≤ p) (hpb : p ≤ (4751/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172543547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5211/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2043/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1608_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
