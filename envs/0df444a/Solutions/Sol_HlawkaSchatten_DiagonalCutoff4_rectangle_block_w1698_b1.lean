-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1698_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:18.509092+00:00
-- url     : https://prove2.me/submissions/1a5ab642-8562-4a1f-bb28-bffa9e49d486

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
theorem support_rectangle_w1698_s3_0 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1456636871/10000000000 : ℝ)*x 0 + (42795627/78125000 : ℝ)*x 1 + (5136624893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1456636871/10000000000 : ℝ)^5207 ≤ (454474354067/5000000000000 : ℝ)^4183 := by
    have hnat : (1456636871 : ℕ)^5207*5000000000000^4183 ≤ 454474354067^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456636871 10000000000 454474354067 5000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42795627/78125000 : ℝ)^5207 ≤ (23636917520047/50000000000000 : ℝ)^4183 := by
    have hnat : (42795627 : ℕ)^5207*50000000000000^4183 ≤ 23636917520047^4183*78125000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42795627 78125000 23636917520047 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136624893/10000000000 : ℝ)^5207 ≤ (1745467114783/4000000000000 : ℝ)^4183 := by
    have hnat : (5136624893 : ℕ)^5207*4000000000000^4183 ≤ 1745467114783^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136624893 10000000000 1745467114783 4000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1456636871/10000000000 : ℝ), (42795627/78125000 : ℝ), (5136624893/10000000000 : ℝ)] ![(454474354067/5000000000000 : ℝ), (23636917520047/50000000000000 : ℝ), (1745467114783/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1456636871/10000000000 : ℝ)|^5207 ≤ (454474354067/5000000000000 : ℝ)^4183
        have hw : |(-1456636871/10000000000 : ℝ)|=(1456636871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42795627/78125000 : ℝ)|^5207 ≤ (23636917520047/50000000000000 : ℝ)^4183
        have hw : |(42795627/78125000 : ℝ)|=(42795627/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136624893/10000000000 : ℝ)|^5207 ≤ (1745467114783/4000000000000 : ℝ)^4183
        have hw : |(5136624893/10000000000 : ℝ)|=(5136624893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_1 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673772303/5000000000 : ℝ)*x 0 + (-408437277/2500000000 : ℝ)*x 1 + (16051953/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673772303/5000000000 : ℝ)^5207 ≤ (45878215063431/100000000000000 : ℝ)^4183 := by
    have hnat : (2673772303 : ℕ)^5207*100000000000000^4183 ≤ 45878215063431^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673772303 5000000000 45878215063431 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408437277/2500000000 : ℝ)^5207 ≤ (5242553170619/50000000000000 : ℝ)^4183 := by
    have hnat : (408437277 : ℕ)^5207*50000000000000^4183 ≤ 5242553170619^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408437277 2500000000 5242553170619 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16051953/31250000 : ℝ)^5207 ≤ (43636678578089/100000000000000 : ℝ)^4183 := by
    have hnat : (16051953 : ℕ)^5207*100000000000000^4183 ≤ 43636678578089^4183*31250000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16051953 31250000 43636678578089 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673772303/5000000000 : ℝ), (-408437277/2500000000 : ℝ), (16051953/31250000 : ℝ)] ![(45878215063431/100000000000000 : ℝ), (5242553170619/50000000000000 : ℝ), (43636678578089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673772303/5000000000 : ℝ)|^5207 ≤ (45878215063431/100000000000000 : ℝ)^4183
        have hw : |(2673772303/5000000000 : ℝ)|=(2673772303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408437277/2500000000 : ℝ)|^5207 ≤ (5242553170619/50000000000000 : ℝ)^4183
        have hw : |(-408437277/2500000000 : ℝ)|=(408437277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16051953/31250000 : ℝ)|^5207 ≤ (43636678578089/100000000000000 : ℝ)^4183
        have hw : |(16051953/31250000 : ℝ)|=(16051953/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_2 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673772311/5000000000 : ℝ)*x 0 + (5136624937/10000000000 : ℝ)*x 1 + (-1633749117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673772311/5000000000 : ℝ)^5207 ≤ (45878215234303/100000000000000 : ℝ)^4183 := by
    have hnat : (2673772311 : ℕ)^5207*100000000000000^4183 ≤ 45878215234303^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673772311 5000000000 45878215234303 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136624937/10000000000 : ℝ)^5207 ≤ (10909169583717/25000000000000 : ℝ)^4183 := by
    have hnat : (5136624937 : ℕ)^5207*25000000000000^4183 ≤ 10909169583717^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136624937 10000000000 10909169583717 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633749117/10000000000 : ℝ)^5207 ≤ (5242553206569/50000000000000 : ℝ)^4183 := by
    have hnat : (1633749117 : ℕ)^5207*50000000000000^4183 ≤ 5242553206569^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633749117 10000000000 5242553206569 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673772311/5000000000 : ℝ), (5136624937/10000000000 : ℝ), (-1633749117/10000000000 : ℝ)] ![(45878215234303/100000000000000 : ℝ), (10909169583717/25000000000000 : ℝ), (5242553206569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673772311/5000000000 : ℝ)|^5207 ≤ (45878215234303/100000000000000 : ℝ)^4183
        have hw : |(2673772311/5000000000 : ℝ)|=(2673772311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136624937/10000000000 : ℝ)|^5207 ≤ (10909169583717/25000000000000 : ℝ)^4183
        have hw : |(5136624937/10000000000 : ℝ)|=(5136624937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1633749117/10000000000 : ℝ)|^5207 ≤ (5242553206569/50000000000000 : ℝ)^4183
        have hw : |(-1633749117/10000000000 : ℝ)|=(1633749117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_3 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4120417647/10000000000 : ℝ)*x 0 + (36576471/100000000 : ℝ)*x 1 + (923974817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4120417647/10000000000 : ℝ)^5207 ≤ (33164901089959/100000000000000 : ℝ)^4183 := by
    have hnat : (4120417647 : ℕ)^5207*100000000000000^4183 ≤ 33164901089959^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120417647 10000000000 33164901089959 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36576471/100000000 : ℝ)^5207 ≤ (1787118919019/6250000000000 : ℝ)^4183 := by
    have hnat : (36576471 : ℕ)^5207*6250000000000^4183 ≤ 1787118919019^4183*100000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36576471 100000000 1787118919019 6250000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923974817/2000000000 : ℝ)^5207 ≤ (7648239240231/20000000000000 : ℝ)^4183 := by
    have hnat : (923974817 : ℕ)^5207*20000000000000^4183 ≤ 7648239240231^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923974817 2000000000 7648239240231 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4120417647/10000000000 : ℝ), (36576471/100000000 : ℝ), (923974817/2000000000 : ℝ)] ![(33164901089959/100000000000000 : ℝ), (1787118919019/6250000000000 : ℝ), (7648239240231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4120417647/10000000000 : ℝ)|^5207 ≤ (33164901089959/100000000000000 : ℝ)^4183
        have hw : |(4120417647/10000000000 : ℝ)|=(4120417647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36576471/100000000 : ℝ)|^5207 ≤ (1787118919019/6250000000000 : ℝ)^4183
        have hw : |(36576471/100000000 : ℝ)|=(36576471/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923974817/2000000000 : ℝ)|^5207 ≤ (7648239240231/20000000000000 : ℝ)^4183
        have hw : |(923974817/2000000000 : ℝ)|=(923974817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_4 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1456793613/10000000000 : ℝ)*x 0 + (5140364227/10000000000 : ℝ)*x 1 + (1368511337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1456793613/10000000000 : ℝ)^5207 ≤ (2272676152291/25000000000000 : ℝ)^4183 := by
    have hnat : (1456793613 : ℕ)^5207*25000000000000^4183 ≤ 2272676152291^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456793613 10000000000 2272676152291 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140364227/10000000000 : ℝ)^5207 ≤ (272976401419/625000000000 : ℝ)^4183 := by
    have hnat : (5140364227 : ℕ)^5207*625000000000^4183 ≤ 272976401419^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140364227 10000000000 272976401419 625000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368511337/2500000000 : ℝ)^5207 ≤ (11808267787953/25000000000000 : ℝ)^4183 := by
    have hnat : (1368511337 : ℕ)^5207*25000000000000^4183 ≤ 11808267787953^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368511337 2500000000 11808267787953 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1456793613/10000000000 : ℝ), (5140364227/10000000000 : ℝ), (1368511337/2500000000 : ℝ)] ![(2272676152291/25000000000000 : ℝ), (272976401419/625000000000 : ℝ), (11808267787953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1456793613/10000000000 : ℝ)|^5207 ≤ (2272676152291/25000000000000 : ℝ)^4183
        have hw : |(-1456793613/10000000000 : ℝ)|=(1456793613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140364227/10000000000 : ℝ)|^5207 ≤ (272976401419/625000000000 : ℝ)^4183
        have hw : |(5140364227/10000000000 : ℝ)|=(5140364227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368511337/2500000000 : ℝ)|^5207 ≤ (11808267787953/25000000000000 : ℝ)^4183
        have hw : |(1368511337/2500000000 : ℝ)|=(1368511337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_5 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657032629/1250000000 : ℝ)*x 0 + (-1296328579/10000000000 : ℝ)*x 1 + (2737022531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657032629/1250000000 : ℝ)^5207 ≤ (11226348958181/25000000000000 : ℝ)^4183 := by
    have hnat : (657032629 : ℕ)^5207*25000000000000^4183 ≤ 11226348958181^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657032629 1250000000 11226348958181 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296328579/10000000000 : ℝ)^5207 ≤ (7861536075229/100000000000000 : ℝ)^4183 := by
    have hnat : (1296328579 : ℕ)^5207*100000000000000^4183 ≤ 7861536075229^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296328579 10000000000 7861536075229 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737022531/5000000000 : ℝ)^5207 ≤ (47233068079937/100000000000000 : ℝ)^4183 := by
    have hnat : (2737022531 : ℕ)^5207*100000000000000^4183 ≤ 47233068079937^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737022531 5000000000 47233068079937 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657032629/1250000000 : ℝ), (-1296328579/10000000000 : ℝ), (2737022531/5000000000 : ℝ)] ![(11226348958181/25000000000000 : ℝ), (7861536075229/100000000000000 : ℝ), (47233068079937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657032629/1250000000 : ℝ)|^5207 ≤ (11226348958181/25000000000000 : ℝ)^4183
        have hw : |(657032629/1250000000 : ℝ)|=(657032629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1296328579/10000000000 : ℝ)|^5207 ≤ (7861536075229/100000000000000 : ℝ)^4183
        have hw : |(-1296328579/10000000000 : ℝ)|=(1296328579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737022531/5000000000 : ℝ)|^5207 ≤ (47233068079937/100000000000000 : ℝ)^4183
        have hw : |(2737022531/5000000000 : ℝ)|=(2737022531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_6 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256260481/10000000000 : ℝ)*x 0 + (1094809087/2000000000 : ℝ)*x 1 + (-51853153/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256260481/10000000000 : ℝ)^5207 ≤ (44905389973057/100000000000000 : ℝ)^4183 := by
    have hnat : (5256260481 : ℕ)^5207*100000000000000^4183 ≤ 44905389973057^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256260481 10000000000 44905389973057 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094809087/2000000000 : ℝ)^5207 ≤ (47233072086263/100000000000000 : ℝ)^4183 := by
    have hnat : (1094809087 : ℕ)^5207*100000000000000^4183 ≤ 47233072086263^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094809087 2000000000 47233072086263 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51853153/400000000 : ℝ)^5207 ≤ (1572307586459/20000000000000 : ℝ)^4183 := by
    have hnat : (51853153 : ℕ)^5207*20000000000000^4183 ≤ 1572307586459^4183*400000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51853153 400000000 1572307586459 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256260481/10000000000 : ℝ), (1094809087/2000000000 : ℝ), (-51853153/400000000 : ℝ)] ![(44905389973057/100000000000000 : ℝ), (47233072086263/100000000000000 : ℝ), (1572307586459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256260481/10000000000 : ℝ)|^5207 ≤ (44905389973057/100000000000000 : ℝ)^4183
        have hw : |(5256260481/10000000000 : ℝ)|=(5256260481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094809087/2000000000 : ℝ)|^5207 ≤ (47233072086263/100000000000000 : ℝ)^4183
        have hw : |(1094809087/2000000000 : ℝ)|=(1094809087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51853153/400000000 : ℝ)|^5207 ≤ (1572307586459/20000000000000 : ℝ)^4183
        have hw : |(-51853153/400000000 : ℝ)|=(51853153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s3_7 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2060430451/5000000000 : ℝ)*x 0 + (4609328463/10000000000 : ℝ)*x 1 + (3668349879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060430451/5000000000 : ℝ)^5207 ≤ (6633868450243/20000000000000 : ℝ)^4183 := by
    have hnat : (2060430451 : ℕ)^5207*20000000000000^4183 ≤ 6633868450243^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060430451 5000000000 6633868450243 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4609328463/10000000000 : ℝ)^5207 ≤ (38132565691991/100000000000000 : ℝ)^4183 := by
    have hnat : (4609328463 : ℕ)^5207*100000000000000^4183 ≤ 38132565691991^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609328463 10000000000 38132565691991 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3668349879/10000000000 : ℝ)^5207 ≤ (3587261506211/12500000000000 : ℝ)^4183 := by
    have hnat : (3668349879 : ℕ)^5207*12500000000000^4183 ≤ 3587261506211^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668349879 10000000000 3587261506211 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2060430451/5000000000 : ℝ), (4609328463/10000000000 : ℝ), (3668349879/10000000000 : ℝ)] ![(6633868450243/20000000000000 : ℝ), (38132565691991/100000000000000 : ℝ), (3587261506211/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2060430451/5000000000 : ℝ)|^5207 ≤ (6633868450243/20000000000000 : ℝ)^4183
        have hw : |(2060430451/5000000000 : ℝ)|=(2060430451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4609328463/10000000000 : ℝ)|^5207 ≤ (38132565691991/100000000000000 : ℝ)^4183
        have hw : |(4609328463/10000000000 : ℝ)|=(4609328463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3668349879/10000000000 : ℝ)|^5207 ≤ (3587261506211/12500000000000 : ℝ)^4183
        have hw : |(3668349879/10000000000 : ℝ)|=(3668349879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1698_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9907/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17179/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4299/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4299/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4299/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4299/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4299/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4299/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9893/100000 : ℝ) ^ (5199/1024 : ℝ) ≤ (792740727861281/100000000000000000000 : ℝ) := by
    have hpowers : (9893/100000 : ℝ)^5199 ≤ (792740727861281/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9893 : ℕ)^5199*100000000000000000000^1024 ≤ 792740727861281^1024*100000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9893 100000 792740727861281 100000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9893/100000 : ℝ)) (X := (792740727861281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4299/25000 : ℝ) ^ (5199/1024 : ℝ) ≤ (13126580419415719/100000000000000000000 : ℝ) := by
    have hpowers : (4299/25000 : ℝ)^5199 ≤ (13126580419415719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4299 : ℕ)^5199*100000000000000000000^1024 ≤ 13126580419415719^1024*25000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4299 25000 13126580419415719 100000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4299/25000 : ℝ)) (X := (13126580419415719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000792740727861281/50000000000000000000 : ℝ) ≤ (10000031227595217/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (50000792740727861281/50000000000000000000 : ℝ)^1024 ≤ (10000031227595217/10000000000000000 : ℝ)^5199 := by
      have hnat : (50000792740727861281 : ℕ)^1024*10000000000000000^5199 ≤ 10000031227595217^5199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000792740727861281 50000000000000000000 10000031227595217 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031227595217/10000000000000000 : ℝ)) (X := (50000792740727861281/50000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013919321147277/100000000000000000 : ℝ) ≤ (250006853523907/250000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (100013919321147277/100000000000000000 : ℝ)^1024 ≤ (250006853523907/250000000000000 : ℝ)^5199 := by
      have hnat : (100013919321147277 : ℕ)^1024*250000000000000^5199 ≤ 250006853523907^5199*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013919321147277 100000000000000000 250006853523907 250000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250006853523907/250000000000000 : ℝ)) (X := (100013919321147277/100000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013126580419415719/50000000000000000000 : ℝ) ≤ (10000517054317343/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (50013126580419415719/50000000000000000000 : ℝ)^1024 ≤ (10000517054317343/10000000000000000 : ℝ)^5199 := by
      have hnat : (50013126580419415719 : ℕ)^1024*10000000000000000^5199 ≤ 10000517054317343^5199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013126580419415719 50000000000000000000 10000517054317343 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000517054317343/10000000000000000 : ℝ)) (X := (50013126580419415719/50000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(792740727861281/100000000000000000000 : ℝ) ≤ ((73025421771365877233/73030000000000000000 : ℝ)+2*(242913361063/730300000000000 : ℝ)*(9893/100000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (73025421771365877233/73030000000000000000 : ℝ)+2*(242913361063/730300000000000 : ℝ)*(9893/100000 : ℝ)=(10000031227595217/10000000000000000 : ℝ) by norm_num, show 1+2*(792740727861281/100000000000000000000 : ℝ)=(50000792740727861281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13126580419415719/100000000000000000000 : ℝ)+(792740727861281/100000000000000000000 : ℝ) ≤ ((73025421771365877233/73030000000000000000 : ℝ)+(242913361063/730300000000000 : ℝ)*((4299/25000 : ℝ)+(9893/100000 : ℝ)))^(5199/1024 : ℝ) := by
    rw [show (73025421771365877233/73030000000000000000 : ℝ)+(242913361063/730300000000000 : ℝ)*((4299/25000 : ℝ)+(9893/100000 : ℝ))=(250006853523907/250000000000000 : ℝ) by norm_num, show 1+(13126580419415719/100000000000000000000 : ℝ)+(792740727861281/100000000000000000000 : ℝ)=(100013919321147277/100000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13126580419415719/100000000000000000000 : ℝ) ≤ ((73025421771365877233/73030000000000000000 : ℝ)+2*(242913361063/730300000000000 : ℝ)*(4299/25000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (73025421771365877233/73030000000000000000 : ℝ)+2*(242913361063/730300000000000 : ℝ)*(4299/25000 : ℝ)=(10000517054317343/10000000000000000 : ℝ) by norm_num, show 1+2*(13126580419415719/100000000000000000000 : ℝ)=(50013126580419415719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73025421771365877233/73030000000000000000 : ℝ)*(X 1 0+X 2 0)+(242913361063/730300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9893/100000 : ℝ)) (hi := (4299/25000 : ℝ)) (c := (73025421771365877233/73030000000000000000 : ℝ)) (alpha := (242913361063/730300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73025421771365877233/73030000000000000000 : ℝ)*(X 0 1+X 2 1)+(242913361063/730300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9893/100000 : ℝ)) (hi := (4299/25000 : ℝ)) (c := (73025421771365877233/73030000000000000000 : ℝ)) (alpha := (242913361063/730300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73025421771365877233/73030000000000000000 : ℝ)*(X 0 2+X 1 2)+(242913361063/730300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9893/100000 : ℝ)) (hi := (4299/25000 : ℝ)) (c := (73025421771365877233/73030000000000000000 : ℝ)) (alpha := (242913361063/730300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1456636871/10000000000 : ℝ)*X 0 0+(42795627/78125000 : ℝ)*X 0 1+(5136624893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673772303/5000000000 : ℝ)*X 1 0+(-408437277/2500000000 : ℝ)*X 1 1+(16051953/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673772311/5000000000 : ℝ)*X 2 0+(5136624937/10000000000 : ℝ)*X 2 1+(-1633749117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4120417647/10000000000 : ℝ)*X 0 0+(36576471/100000000 : ℝ)*X 0 1+(923974817/2000000000 : ℝ)*X 0 2+(4120417647/10000000000 : ℝ)*X 1 0+(36576471/100000000 : ℝ)*X 1 1+(923974817/2000000000 : ℝ)*X 1 2+(4120417647/10000000000 : ℝ)*X 2 0+(36576471/100000000 : ℝ)*X 2 1+(923974817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1456793613/10000000000 : ℝ)*X 0 0+(5140364227/10000000000 : ℝ)*X 0 1+(1368511337/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((657032629/1250000000 : ℝ)*X 1 0+(-1296328579/10000000000 : ℝ)*X 1 1+(2737022531/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256260481/10000000000 : ℝ)*X 2 0+(1094809087/2000000000 : ℝ)*X 2 1+(-51853153/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2060430451/5000000000 : ℝ)*X 0 0+(4609328463/10000000000 : ℝ)*X 0 1+(3668349879/10000000000 : ℝ)*X 0 2+(2060430451/5000000000 : ℝ)*X 1 0+(4609328463/10000000000 : ℝ)*X 1 1+(3668349879/10000000000 : ℝ)*X 1 2+(2060430451/5000000000 : ℝ)*X 2 0+(4609328463/10000000000 : ℝ)*X 2 1+(3668349879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2044495014619320729877348539/182575000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157744681/10000000000000 : ℝ)*(base19) + (1563306359/100000000000000 : ℝ)*(base23) + (12250837/100000000000000 : ℝ)*(lower2) + (13026843/5000000000000 : ℝ)*(upper3) + (119789717/50000000000000 : ℝ)*(upper5) + (198499973405161/10000000000000 : ℝ)*(major0) + (198499973405161/10000000000000 : ℝ)*(major1) + (198499973405161/10000000000000 : ℝ)*(major2) + (1465357932580939/50000000000000 : ℝ)*(sp0) + (183170617787099/6250000000000 : ℝ)*(sp1) + (732682474683509/25000000000000 : ℝ)*(sp2) + (519630789659157/50000000000000 : ℝ)*(sp3) + (3899219629/25000000000000 : ℝ)*(sp4) + (3026737079/50000000000000 : ℝ)*(sp7) + (1039267632792471/100000000000000 : ℝ)*(f.failure) + (1465365731020197/50000000000000 : ℝ)*(f.sum) + (21964516399499/3651500000000000000000000000 : ℝ)*base66 + (5026265258847300487/730300000000000000000000000000000 : ℝ)*base68 + (137148730230699513/730300000000000000000000000000000 : ℝ)*base69 + (2674121682104500487/730300000000000000000000000000000 : ℝ)*base72 + (623437680069/182575000000000000000000000 : ℝ)*base74 + (3653023568114700487/730300000000000000000000000000000 : ℝ)*base76 + (7201066242290900487/730300000000000000000000000000000 : ℝ)*base78 + (8146141790556900487/730300000000000000000000000000000 : ℝ)*base80 + (6004677977897/3651500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2846531/10000000000000000000000 : ℝ)*base89 + (2846531/10000000000000000000000 : ℝ)*base91 + (2846531/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123297288957958066006659/9128750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1879301369/100000000000000 : ℝ)*(base19) + (229268421/12500000000000 : ℝ)*(base23) + (509854043/100000000000000 : ℝ)*(lower1) + (206229227/100000000000000 : ℝ)*(upper3) + (4830829/3125000000000 : ℝ)*(lower4) + (159885323/50000000000000 : ℝ)*(upper5) + (507446754696763/25000000000000 : ℝ)*(major0) + (507446754696763/25000000000000 : ℝ)*(major1) + (507446754696763/25000000000000 : ℝ)*(major2) + (1445377701/100000000000000 : ℝ)*(sp1) + (1498428548662547/50000000000000 : ℝ)*(sp4) + (374606721580753/12500000000000 : ℝ)*(sp5) + (1498427631588863/50000000000000 : ℝ)*(sp6) + (106271649003297/10000000000000 : ℝ)*(sp7) + (106271649003297/10000000000000 : ℝ)*(f.failure) + (1498428548662547/50000000000000 : ℝ)*(f.sum) + (65163005517253/18257500000000000000000000000 : ℝ)*base65 + (4491191417621396779/1825750000000000000000000000000000 : ℝ)*base67 + (8802890165849103221/1825750000000000000000000000000000 : ℝ)*base70 + (5709388295371896779/1825750000000000000000000000000000 : ℝ)*base71 + (12297497959843/18257500000000000000000000000 : ℝ)*base73 + (9672261625148896779/1825750000000000000000000000000000 : ℝ)*base75 + (784948017002103221/1825750000000000000000000000000000 : ℝ)*base78 + (2842788770132603221/1825750000000000000000000000000000 : ℝ)*base80 + (28440296789019/9128750000000000000000000000 : ℝ)*base81 + (4458283/1000000000000000000000 : ℝ)*base90 + (4458283/1000000000000000000000 : ℝ)*base92 + (4458283/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1698_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9907/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17179/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1698_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1698_s4_0 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1456645827/10000000000 : ℝ)*x 0 + (219112249/400000000 : ℝ)*x 1 + (1284163221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1456645827/10000000000 : ℝ)^5207 ≤ (9089556648169/100000000000000 : ℝ)^4183 := by
    have hnat : (1456645827 : ℕ)^5207*100000000000000^4183 ≤ 9089556648169^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456645827 10000000000 9089556648169 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219112249/400000000 : ℝ)^5207 ≤ (47273469457453/100000000000000 : ℝ)^4183 := by
    have hnat : (219112249 : ℕ)^5207*100000000000000^4183 ≤ 47273469457453^4183*400000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219112249 400000000 47273469457453 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284163221/2500000000 : ℝ)^5207 ≤ (21818486934969/50000000000000 : ℝ)^4183 := by
    have hnat : (1284163221 : ℕ)^5207*50000000000000^4183 ≤ 21818486934969^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284163221 2500000000 21818486934969 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1456645827/10000000000 : ℝ), (219112249/400000000 : ℝ), (1284163221/2500000000 : ℝ)] ![(9089556648169/100000000000000 : ℝ), (47273469457453/100000000000000 : ℝ), (21818486934969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1456645827/10000000000 : ℝ)|^5207 ≤ (9089556648169/100000000000000 : ℝ)^4183
        have hw : |(-1456645827/10000000000 : ℝ)|=(1456645827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219112249/400000000 : ℝ)|^5207 ≤ (47273469457453/100000000000000 : ℝ)^4183
        have hw : |(219112249/400000000 : ℝ)|=(219112249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284163221/2500000000 : ℝ)|^5207 ≤ (21818486934969/50000000000000 : ℝ)^4183
        have hw : |(1284163221/2500000000 : ℝ)|=(1284163221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_1 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347535987/10000000000 : ℝ)*x 0 + (-1633725789/10000000000 : ℝ)*x 1 + (5136651281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347535987/10000000000 : ℝ)^5207 ≤ (917562460333/2000000000000 : ℝ)^4183 := by
    have hnat : (5347535987 : ℕ)^5207*2000000000000^4183 ≤ 917562460333^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347535987 10000000000 917562460333 2000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1633725789/10000000000 : ℝ)^5207 ≤ (2621230012079/25000000000000 : ℝ)^4183 := by
    have hnat : (1633725789 : ℕ)^5207*25000000000000^4183 ≤ 2621230012079^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633725789 10000000000 2621230012079 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136651281/10000000000 : ℝ)^5207 ≤ (21818478459229/50000000000000 : ℝ)^4183 := by
    have hnat : (5136651281 : ℕ)^5207*50000000000000^4183 ≤ 21818478459229^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136651281 10000000000 21818478459229 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347535987/10000000000 : ℝ), (-1633725789/10000000000 : ℝ), (5136651281/10000000000 : ℝ)] ![(917562460333/2000000000000 : ℝ), (2621230012079/25000000000000 : ℝ), (21818478459229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347535987/10000000000 : ℝ)|^5207 ≤ (917562460333/2000000000000 : ℝ)^4183
        have hw : |(5347535987/10000000000 : ℝ)|=(5347535987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1633725789/10000000000 : ℝ)|^5207 ≤ (2621230012079/25000000000000 : ℝ)^4183
        have hw : |(-1633725789/10000000000 : ℝ)|=(1633725789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136651281/10000000000 : ℝ)|^5207 ≤ (21818478459229/50000000000000 : ℝ)^4183
        have hw : |(5136651281/10000000000 : ℝ)|=(5136651281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_2 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336883627/2500000000 : ℝ)*x 0 + (2568326411/5000000000 : ℝ)*x 1 + (-816862863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336883627/2500000000 : ℝ)^5207 ≤ (11469526805411/25000000000000 : ℝ)^4183 := by
    have hnat : (1336883627 : ℕ)^5207*25000000000000^4183 ≤ 11469526805411^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336883627 2500000000 11469526805411 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568326411/5000000000 : ℝ)^5207 ≤ (21818486607149/50000000000000 : ℝ)^4183 := by
    have hnat : (2568326411 : ℕ)^5207*50000000000000^4183 ≤ 21818486607149^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568326411 5000000000 21818486607149 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (816862863/5000000000 : ℝ)^5207 ≤ (10484919545017/100000000000000 : ℝ)^4183 := by
    have hnat : (816862863 : ℕ)^5207*100000000000000^4183 ≤ 10484919545017^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816862863 5000000000 10484919545017 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336883627/2500000000 : ℝ), (2568326411/5000000000 : ℝ), (-816862863/5000000000 : ℝ)] ![(11469526805411/25000000000000 : ℝ), (21818486607149/50000000000000 : ℝ), (10484919545017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336883627/2500000000 : ℝ)|^5207 ≤ (11469526805411/25000000000000 : ℝ)^4183
        have hw : |(1336883627/2500000000 : ℝ)|=(1336883627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568326411/5000000000 : ℝ)|^5207 ≤ (21818486607149/50000000000000 : ℝ)^4183
        have hw : |(2568326411/5000000000 : ℝ)|=(2568326411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-816862863/5000000000 : ℝ)|^5207 ≤ (10484919545017/100000000000000 : ℝ)^4183
        have hw : |(-816862863/5000000000 : ℝ)|=(816862863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_3 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206021201/500000000 : ℝ)*x 0 + (914433379/2500000000 : ℝ)*x 1 + (4619786273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206021201/500000000 : ℝ)^5207 ≤ (33164964942941/100000000000000 : ℝ)^4183 := by
    have hnat : (206021201 : ℕ)^5207*100000000000000^4183 ≤ 33164964942941^4183*500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206021201 500000000 33164964942941 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914433379/2500000000 : ℝ)^5207 ≤ (28594743647697/100000000000000 : ℝ)^4183 := by
    have hnat : (914433379 : ℕ)^5207*100000000000000^4183 ≤ 28594743647697^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914433379 2500000000 28594743647697 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4619786273/10000000000 : ℝ)^5207 ≤ (38240291398427/100000000000000 : ℝ)^4183 := by
    have hnat : (4619786273 : ℕ)^5207*100000000000000^4183 ≤ 38240291398427^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619786273 10000000000 38240291398427 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206021201/500000000 : ℝ), (914433379/2500000000 : ℝ), (4619786273/10000000000 : ℝ)] ![(33164964942941/100000000000000 : ℝ), (28594743647697/100000000000000 : ℝ), (38240291398427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206021201/500000000 : ℝ)|^5207 ≤ (33164964942941/100000000000000 : ℝ)^4183
        have hw : |(206021201/500000000 : ℝ)|=(206021201/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(914433379/2500000000 : ℝ)|^5207 ≤ (28594743647697/100000000000000 : ℝ)^4183
        have hw : |(914433379/2500000000 : ℝ)|=(914433379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4619786273/10000000000 : ℝ)|^5207 ≤ (38240291398427/100000000000000 : ℝ)^4183
        have hw : |(4619786273/10000000000 : ℝ)|=(4619786273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_4 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-364200723/2500000000 : ℝ)*x 0 + (5140390473/10000000000 : ℝ)*x 1 + (5474012793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (364200723/2500000000 : ℝ)^5207 ≤ (1818155337367/20000000000000 : ℝ)^4183 := by
    have hnat : (364200723 : ℕ)^5207*20000000000000^4183 ≤ 1818155337367^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364200723 2500000000 1818155337367 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140390473/10000000000 : ℝ)^5207 ≤ (21838250911871/50000000000000 : ℝ)^4183 := by
    have hnat : (5140390473 : ℕ)^5207*50000000000000^4183 ≤ 21838250911871^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140390473 10000000000 21838250911871 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474012793/10000000000 : ℝ)^5207 ≤ (5904090185577/12500000000000 : ℝ)^4183 := by
    have hnat : (5474012793 : ℕ)^5207*12500000000000^4183 ≤ 5904090185577^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474012793 10000000000 5904090185577 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-364200723/2500000000 : ℝ), (5140390473/10000000000 : ℝ), (5474012793/10000000000 : ℝ)] ![(1818155337367/20000000000000 : ℝ), (21838250911871/50000000000000 : ℝ), (5904090185577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-364200723/2500000000 : ℝ)|^5207 ≤ (1818155337367/20000000000000 : ℝ)^4183
        have hw : |(-364200723/2500000000 : ℝ)|=(364200723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140390473/10000000000 : ℝ)|^5207 ≤ (21838250911871/50000000000000 : ℝ)^4183
        have hw : |(5140390473/10000000000 : ℝ)|=(5140390473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474012793/10000000000 : ℝ)|^5207 ≤ (5904090185577/12500000000000 : ℝ)^4183
        have hw : |(5474012793/10000000000 : ℝ)|=(5474012793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_5 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256267863/10000000000 : ℝ)*x 0 + (-648182423/5000000000 : ℝ)*x 1 + (5474012809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256267863/10000000000 : ℝ)^5207 ≤ (8981093695543/20000000000000 : ℝ)^4183 := by
    have hnat : (5256267863 : ℕ)^5207*20000000000000^4183 ≤ 8981093695543^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256267863 10000000000 8981093695543 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648182423/5000000000 : ℝ)^5207 ≤ (7861809857391/100000000000000 : ℝ)^4183 := by
    have hnat : (648182423 : ℕ)^5207*100000000000000^4183 ≤ 7861809857391^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648182423 5000000000 7861809857391 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474012809/10000000000 : ℝ)^5207 ≤ (47232721656469/100000000000000 : ℝ)^4183 := by
    have hnat : (5474012809 : ℕ)^5207*100000000000000^4183 ≤ 47232721656469^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474012809 10000000000 47232721656469 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256267863/10000000000 : ℝ), (-648182423/5000000000 : ℝ), (5474012809/10000000000 : ℝ)] ![(8981093695543/20000000000000 : ℝ), (7861809857391/100000000000000 : ℝ), (47232721656469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256267863/10000000000 : ℝ)|^5207 ≤ (8981093695543/20000000000000 : ℝ)^4183
        have hw : |(5256267863/10000000000 : ℝ)|=(5256267863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-648182423/5000000000 : ℝ)|^5207 ≤ (7861809857391/100000000000000 : ℝ)^4183
        have hw : |(-648182423/5000000000 : ℝ)|=(648182423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474012809/10000000000 : ℝ)|^5207 ≤ (47232721656469/100000000000000 : ℝ)^4183
        have hw : |(5474012809/10000000000 : ℝ)|=(5474012809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_6 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262813393/500000000 : ℝ)*x 0 + (684251601/1250000000 : ℝ)*x 1 + (-25927297/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262813393/500000000 : ℝ)^5207 ≤ (44905468445811/100000000000000 : ℝ)^4183 := by
    have hnat : (262813393 : ℕ)^5207*100000000000000^4183 ≤ 44905468445811^4183*500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262813393 500000000 44905468445811 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684251601/1250000000 : ℝ)^5207 ≤ (1476022551429/3125000000000 : ℝ)^4183 := by
    have hnat : (684251601 : ℕ)^5207*3125000000000^4183 ≤ 1476022551429^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684251601 1250000000 1476022551429 3125000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25927297/200000000 : ℝ)^5207 ≤ (1965452471897/25000000000000 : ℝ)^4183 := by
    have hnat : (25927297 : ℕ)^5207*25000000000000^4183 ≤ 1965452471897^4183*200000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25927297 200000000 1965452471897 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262813393/500000000 : ℝ), (684251601/1250000000 : ℝ), (-25927297/200000000 : ℝ)] ![(44905468445811/100000000000000 : ℝ), (1476022551429/3125000000000 : ℝ), (1965452471897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262813393/500000000 : ℝ)|^5207 ≤ (44905468445811/100000000000000 : ℝ)^4183
        have hw : |(262813393/500000000 : ℝ)|=(262813393/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684251601/1250000000 : ℝ)|^5207 ≤ (1476022551429/3125000000000 : ℝ)^4183
        have hw : |(684251601/1250000000 : ℝ)|=(684251601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-25927297/200000000 : ℝ)|^5207 ≤ (1965452471897/25000000000000 : ℝ)^4183
        have hw : |(-25927297/200000000 : ℝ)|=(25927297/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s4_7 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4120866519/10000000000 : ℝ)*x 0 + (4609245691/10000000000 : ℝ)*x 1 + (917107907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4120866519/10000000000 : ℝ)^5207 ≤ (33169398531089/100000000000000 : ℝ)^4183 := by
    have hnat : (4120866519 : ℕ)^5207*100000000000000^4183 ≤ 33169398531089^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120866519 10000000000 33169398531089 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4609245691/10000000000 : ℝ)^5207 ≤ (9532928324403/25000000000000 : ℝ)^4183 := by
    have hnat : (4609245691 : ℕ)^5207*25000000000000^4183 ≤ 9532928324403^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609245691 10000000000 9532928324403 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917107907/2500000000 : ℝ)^5207 ≤ (14349444073007/50000000000000 : ℝ)^4183 := by
    have hnat : (917107907 : ℕ)^5207*50000000000000^4183 ≤ 14349444073007^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917107907 2500000000 14349444073007 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4120866519/10000000000 : ℝ), (4609245691/10000000000 : ℝ), (917107907/2500000000 : ℝ)] ![(33169398531089/100000000000000 : ℝ), (9532928324403/25000000000000 : ℝ), (14349444073007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4120866519/10000000000 : ℝ)|^5207 ≤ (33169398531089/100000000000000 : ℝ)^4183
        have hw : |(4120866519/10000000000 : ℝ)|=(4120866519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4609245691/10000000000 : ℝ)|^5207 ≤ (9532928324403/25000000000000 : ℝ)^4183
        have hw : |(4609245691/10000000000 : ℝ)|=(4609245691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(917107907/2500000000 : ℝ)|^5207 ≤ (14349444073007/50000000000000 : ℝ)^4183
        have hw : |(917107907/2500000000 : ℝ)|=(917107907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1698_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2477/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8589/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9907/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17179/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9907/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9907/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17179/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9907/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9907/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17179/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9907/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9907/100000 : ℝ) ^ (5199/1024 : ℝ) ≤ (798452935076427/100000000000000000000 : ℝ) := by
    have hpowers : (9907/100000 : ℝ)^5199 ≤ (798452935076427/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9907 : ℕ)^5199*100000000000000000000^1024 ≤ 798452935076427^1024*100000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9907 100000 798452935076427 100000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9907/100000 : ℝ)) (X := (798452935076427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17179/100000 : ℝ) ^ (5199/1024 : ℝ) ≤ (3265206774149339/25000000000000000000 : ℝ) := by
    have hpowers : (17179/100000 : ℝ)^5199 ≤ (3265206774149339/25000000000000000000 : ℝ)^1024 := by
      have hnat : (17179 : ℕ)^5199*25000000000000000000^1024 ≤ 3265206774149339^1024*100000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17179 100000 3265206774149339 25000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17179/100000 : ℝ)) (X := (3265206774149339/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000798452935076427/50000000000000000000 : ℝ) ≤ (10000031452608699/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (50000798452935076427/50000000000000000000 : ℝ)^1024 ≤ (10000031452608699/10000000000000000 : ℝ)^5199 := by
      have hnat : (50000798452935076427 : ℕ)^1024*10000000000000000^5199 ≤ 10000031452608699^5199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000798452935076427 50000000000000000000 10000031452608699 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031452608699/10000000000000000 : ℝ)) (X := (50000798452935076427/50000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013859280031673783/100000000000000000000 : ℝ) ≤ (10000272958512623/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (100013859280031673783/100000000000000000000 : ℝ)^1024 ≤ (10000272958512623/10000000000000000 : ℝ)^5199 := by
      have hnat : (100013859280031673783 : ℕ)^1024*10000000000000000^5199 ≤ 10000272958512623^5199*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013859280031673783 100000000000000000000 10000272958512623 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000272958512623/10000000000000000 : ℝ)) (X := (100013859280031673783/100000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503265206774149339/12500000000000000000 : ℝ) ≤ (10000514464416547/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (12503265206774149339/12500000000000000000 : ℝ)^1024 ≤ (10000514464416547/10000000000000000 : ℝ)^5199 := by
      have hnat : (12503265206774149339 : ℕ)^1024*10000000000000000^5199 ≤ 10000514464416547^5199*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503265206774149339 12500000000000000000 10000514464416547 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000514464416547/10000000000000000 : ℝ)) (X := (12503265206774149339/12500000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(798452935076427/100000000000000000000 : ℝ) ≤ ((1136178805084220453/1136250000000000000 : ℝ)+2*(60376475981/181800000000000 : ℝ)*(9907/100000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (1136178805084220453/1136250000000000000 : ℝ)+2*(60376475981/181800000000000 : ℝ)*(9907/100000 : ℝ)=(10000031452608699/10000000000000000 : ℝ) by norm_num, show 1+2*(798452935076427/100000000000000000000 : ℝ)=(50000798452935076427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3265206774149339/25000000000000000000 : ℝ)+(798452935076427/100000000000000000000 : ℝ) ≤ ((1136178805084220453/1136250000000000000 : ℝ)+(60376475981/181800000000000 : ℝ)*((17179/100000 : ℝ)+(9907/100000 : ℝ)))^(5199/1024 : ℝ) := by
    rw [show (1136178805084220453/1136250000000000000 : ℝ)+(60376475981/181800000000000 : ℝ)*((17179/100000 : ℝ)+(9907/100000 : ℝ))=(10000272958512623/10000000000000000 : ℝ) by norm_num, show 1+(3265206774149339/25000000000000000000 : ℝ)+(798452935076427/100000000000000000000 : ℝ)=(100013859280031673783/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3265206774149339/25000000000000000000 : ℝ) ≤ ((1136178805084220453/1136250000000000000 : ℝ)+2*(60376475981/181800000000000 : ℝ)*(17179/100000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (1136178805084220453/1136250000000000000 : ℝ)+2*(60376475981/181800000000000 : ℝ)*(17179/100000 : ℝ)=(10000514464416547/10000000000000000 : ℝ) by norm_num, show 1+2*(3265206774149339/25000000000000000000 : ℝ)=(12503265206774149339/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1136178805084220453/1136250000000000000 : ℝ)*(X 1 0+X 2 0)+(60376475981/181800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9907/100000 : ℝ)) (hi := (17179/100000 : ℝ)) (c := (1136178805084220453/1136250000000000000 : ℝ)) (alpha := (60376475981/181800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1136178805084220453/1136250000000000000 : ℝ)*(X 0 1+X 2 1)+(60376475981/181800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9907/100000 : ℝ)) (hi := (17179/100000 : ℝ)) (c := (1136178805084220453/1136250000000000000 : ℝ)) (alpha := (60376475981/181800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1136178805084220453/1136250000000000000 : ℝ)*(X 0 2+X 1 2)+(60376475981/181800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9907/100000 : ℝ)) (hi := (17179/100000 : ℝ)) (c := (1136178805084220453/1136250000000000000 : ℝ)) (alpha := (60376475981/181800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1456645827/10000000000 : ℝ)*X 0 0+(219112249/400000000 : ℝ)*X 0 1+(1284163221/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347535987/10000000000 : ℝ)*X 1 0+(-1633725789/10000000000 : ℝ)*X 1 1+(5136651281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336883627/2500000000 : ℝ)*X 2 0+(2568326411/5000000000 : ℝ)*X 2 1+(-816862863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((206021201/500000000 : ℝ)*X 0 0+(914433379/2500000000 : ℝ)*X 0 1+(4619786273/10000000000 : ℝ)*X 0 2+(206021201/500000000 : ℝ)*X 1 0+(914433379/2500000000 : ℝ)*X 1 1+(4619786273/10000000000 : ℝ)*X 1 2+(206021201/500000000 : ℝ)*X 2 0+(914433379/2500000000 : ℝ)*X 2 1+(4619786273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-364200723/2500000000 : ℝ)*X 0 0+(5140390473/10000000000 : ℝ)*X 0 1+(5474012793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256267863/10000000000 : ℝ)*X 1 0+(-648182423/5000000000 : ℝ)*X 1 1+(5474012809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262813393/500000000 : ℝ)*X 2 0+(684251601/1250000000 : ℝ)*X 2 1+(-25927297/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4120866519/10000000000 : ℝ)*X 0 0+(4609245691/10000000000 : ℝ)*X 0 1+(917107907/2500000000 : ℝ)*X 0 2+(4120866519/10000000000 : ℝ)*X 1 0+(4609245691/10000000000 : ℝ)*X 1 1+(917107907/2500000000 : ℝ)*X 1 2+(4120866519/10000000000 : ℝ)*X 2 0+(4609245691/10000000000 : ℝ)*X 2 1+(917107907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21015233197551268529543/3030000000000000000000000000 : ℝ) := by norm_num
    linear_combination (597102181/50000000000000 : ℝ)*(base19) + (106569287/20000000000000 : ℝ)*(base23) + (110906207/100000000000000 : ℝ)*(upper3) + (83618843/100000000000000 : ℝ)*(lower4) + (183279539/100000000000000 : ℝ)*(upper5) + (1985340889364747/100000000000000 : ℝ)*(major0) + (1985340889364747/100000000000000 : ℝ)*(major1) + (1985340889364747/100000000000000 : ℝ)*(major2) + (2931235299269153/100000000000000 : ℝ)*(sp0) + (293123410506479/10000000000000 : ℝ)*(sp1) + (117249374209483/4000000000000 : ℝ)*(sp2) + (1039445907690883/100000000000000 : ℝ)*(sp3) + (411185643/100000000000000 : ℝ)*(sp6) + (340578767/100000000000000 : ℝ)*(sp7) + (20788924965393/2000000000000 : ℝ)*(f.failure) + (2931235299269153/100000000000000 : ℝ)*(f.sum) + (59463659524373/9090000000000000000000000000 : ℝ)*base66 + (382409649579614141/113625000000000000000000000000000 : ℝ)*base67 + (126273454737989141/113625000000000000000000000000000 : ℝ)*base69 + (543208508097510859/113625000000000000000000000000000 : ℝ)*base72 + (40297535058457/9090000000000000000000000000 : ℝ)*base73 + (774866686882739141/113625000000000000000000000000000 : ℝ)*base75 + (18967795366260859/113625000000000000000000000000000 : ℝ)*base78 + (46139964923010859/113625000000000000000000000000000 : ℝ)*base80 + (1995516370657/9090000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1189627/200000000000000000000 : ℝ)*base90 + (1189627/200000000000000000000 : ℝ)*base92 + (1189627/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2476025337018856801737/252500000000000000000000000 : ℝ) := by norm_num
    linear_combination (68245109/5000000000000 : ℝ)*(base19) + (1483107733/100000000000000 : ℝ)*(base23) + (205543637/50000000000000 : ℝ)*(lower1) + (52865381/25000000000000 : ℝ)*(upper3) + (6702481/12500000000000 : ℝ)*(lower4) + (25291027/12500000000000 : ℝ)*(upper5) + (253768333872189/12500000000000 : ℝ)*(major0) + (253768333872189/12500000000000 : ℝ)*(major1) + (253768333872189/12500000000000 : ℝ)*(major2) + (20623913/2000000000000 : ℝ)*(sp2) + (149869411267041/5000000000000 : ℝ)*(sp4) + (37467335755483/1250000000000 : ℝ)*(sp5) + (2997385711037437/100000000000000 : ℝ)*(sp6) + (531452394873081/50000000000000 : ℝ)*(sp7) + (531452394873081/50000000000000 : ℝ)*(f.failure) + (149869411267041/5000000000000 : ℝ)*(f.sum) + (2619667543321/757500000000000000000000000 : ℝ)*base65 + (40271891130485539/4734375000000000000000000000000 : ℝ)*base67 + (21161482881733211/4734375000000000000000000000000 : ℝ)*base70 + (177790900183798039/4734375000000000000000000000000 : ℝ)*base71 + (4200312596341/757500000000000000000000000 : ℝ)*base73 + (93376938170795711/4734375000000000000000000000000 : ℝ)*base76 + (14987825224014461/4734375000000000000000000000000 : ℝ)*base78 + (19411716295985539/4734375000000000000000000000000 : ℝ)*base79 + (3199661244211/757500000000000000000000000 : ℝ)*base81 + (16358259/5000000000000000000000 : ℝ)*base90 + (16358259/5000000000000000000000 : ℝ)*base92 + (16358259/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1698_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17179/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2477/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8589/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1698_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1698_box_0 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1128433451/10000000000 : ℝ)*x 0 + (1355916413/2500000000 : ℝ)*x 1 + (1355916377/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128433451/10000000000 : ℝ)^5207 ≤ (6614875922081/100000000000000 : ℝ)^4183 := by
    have hnat : (1128433451 : ℕ)^5207*100000000000000^4183 ≤ 6614875922081^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128433451 10000000000 6614875922081 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355916413/2500000000 : ℝ)^5207 ≤ (5836570350771/12500000000000 : ℝ)^4183 := by
    have hnat : (1355916413 : ℕ)^5207*12500000000000^4183 ≤ 5836570350771^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355916413 2500000000 5836570350771 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355916377/2500000000 : ℝ)^5207 ≤ (23346280631493/50000000000000 : ℝ)^4183 := by
    have hnat : (1355916377 : ℕ)^5207*50000000000000^4183 ≤ 23346280631493^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355916377 2500000000 23346280631493 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1128433451/10000000000 : ℝ), (1355916413/2500000000 : ℝ), (1355916377/2500000000 : ℝ)] ![(6614875922081/100000000000000 : ℝ), (5836570350771/12500000000000 : ℝ), (23346280631493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1128433451/10000000000 : ℝ)|^5207 ≤ (6614875922081/100000000000000 : ℝ)^4183
        have hw : |(-1128433451/10000000000 : ℝ)|=(1128433451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355916413/2500000000 : ℝ)|^5207 ≤ (5836570350771/12500000000000 : ℝ)^4183
        have hw : |(1355916413/2500000000 : ℝ)|=(1355916413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355916377/2500000000 : ℝ)|^5207 ≤ (23346280631493/50000000000000 : ℝ)^4183
        have hw : |(1355916377/2500000000 : ℝ)|=(1355916377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_1 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612934079/5000000000 : ℝ)*x 0 + (-704764391/5000000000 : ℝ)*x 1 + (5423665513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612934079/5000000000 : ℝ)^5207 ≤ (11145602186451/25000000000000 : ℝ)^4183 := by
    have hnat : (2612934079 : ℕ)^5207*25000000000000^4183 ≤ 11145602186451^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612934079 5000000000 11145602186451 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (704764391/5000000000 : ℝ)^5207 ≤ (4362514965853/50000000000000 : ℝ)^4183 := by
    have hnat : (704764391 : ℕ)^5207*50000000000000^4183 ≤ 4362514965853^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704764391 5000000000 4362514965853 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423665513/10000000000 : ℝ)^5207 ≤ (46692561316569/100000000000000 : ℝ)^4183 := by
    have hnat : (5423665513 : ℕ)^5207*100000000000000^4183 ≤ 46692561316569^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423665513 10000000000 46692561316569 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612934079/5000000000 : ℝ), (-704764391/5000000000 : ℝ), (5423665513/10000000000 : ℝ)] ![(11145602186451/25000000000000 : ℝ), (4362514965853/50000000000000 : ℝ), (46692561316569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612934079/5000000000 : ℝ)|^5207 ≤ (11145602186451/25000000000000 : ℝ)^4183
        have hw : |(2612934079/5000000000 : ℝ)|=(2612934079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-704764391/5000000000 : ℝ)|^5207 ≤ (4362514965853/50000000000000 : ℝ)^4183
        have hw : |(-704764391/5000000000 : ℝ)|=(704764391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423665513/10000000000 : ℝ)|^5207 ≤ (46692561316569/100000000000000 : ℝ)^4183
        have hw : |(5423665513/10000000000 : ℝ)|=(5423665513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_2 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612934081/5000000000 : ℝ)*x 0 + (1355916383/2500000000 : ℝ)*x 1 + (-1409528749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612934081/5000000000 : ℝ)^5207 ≤ (22291204394141/50000000000000 : ℝ)^4183 := by
    have hnat : (2612934081 : ℕ)^5207*50000000000000^4183 ≤ 22291204394141^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612934081 5000000000 22291204394141 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355916383/2500000000 : ℝ)^5207 ≤ (46692561520183/100000000000000 : ℝ)^4183 := by
    have hnat : (1355916383 : ℕ)^5207*100000000000000^4183 ≤ 46692561520183^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355916383 2500000000 46692561520183 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1409528749/10000000000 : ℝ)^5207 ≤ (8725029677429/100000000000000 : ℝ)^4183 := by
    have hnat : (1409528749 : ℕ)^5207*100000000000000^4183 ≤ 8725029677429^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409528749 10000000000 8725029677429 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612934081/5000000000 : ℝ), (1355916383/2500000000 : ℝ), (-1409528749/10000000000 : ℝ)] ![(22291204394141/50000000000000 : ℝ), (46692561520183/100000000000000 : ℝ), (8725029677429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612934081/5000000000 : ℝ)|^5207 ≤ (22291204394141/50000000000000 : ℝ)^4183
        have hw : |(2612934081/5000000000 : ℝ)|=(2612934081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355916383/2500000000 : ℝ)|^5207 ≤ (46692561520183/100000000000000 : ℝ)^4183
        have hw : |(1355916383/2500000000 : ℝ)|=(1355916383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1409528749/10000000000 : ℝ)|^5207 ≤ (8725029677429/100000000000000 : ℝ)^4183
        have hw : |(-1409528749/10000000000 : ℝ)|=(1409528749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_3 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4503672913/10000000000 : ℝ)*x 0 + (3951012149/10000000000 : ℝ)*x 1 + (3951012139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503672913/10000000000 : ℝ)^5207 ≤ (18523791168767/50000000000000 : ℝ)^4183 := by
    have hnat : (4503672913 : ℕ)^5207*50000000000000^4183 ≤ 18523791168767^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503672913 10000000000 18523791168767 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3951012149/10000000000 : ℝ)^5207 ≤ (3934526109429/12500000000000 : ℝ)^4183 := by
    have hnat : (3951012149 : ℕ)^5207*12500000000000^4183 ≤ 3934526109429^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3951012149 10000000000 3934526109429 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3951012139/10000000000 : ℝ)^5207 ≤ (31476208776263/100000000000000 : ℝ)^4183 := by
    have hnat : (3951012139 : ℕ)^5207*100000000000000^4183 ≤ 31476208776263^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3951012139 10000000000 31476208776263 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503672913/10000000000 : ℝ), (3951012149/10000000000 : ℝ), (3951012139/10000000000 : ℝ)] ![(18523791168767/50000000000000 : ℝ), (3934526109429/12500000000000 : ℝ), (31476208776263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503672913/10000000000 : ℝ)|^5207 ≤ (18523791168767/50000000000000 : ℝ)^4183
        have hw : |(4503672913/10000000000 : ℝ)|=(4503672913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3951012149/10000000000 : ℝ)|^5207 ≤ (3934526109429/12500000000000 : ℝ)^4183
        have hw : |(3951012149/10000000000 : ℝ)|=(3951012149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3951012139/10000000000 : ℝ)|^5207 ≤ (31476208776263/100000000000000 : ℝ)^4183
        have hw : |(3951012139/10000000000 : ℝ)|=(3951012139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_4 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-902842103/5000000000 : ℝ)*x 0 + (517680999/1000000000 : ℝ)*x 1 + (1035362113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902842103/5000000000 : ℝ)^5207 ≤ (11875924488089/100000000000000 : ℝ)^4183 := by
    have hnat : (902842103 : ℕ)^5207*100000000000000^4183 ≤ 11875924488089^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902842103 5000000000 11875924488089 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517680999/1000000000 : ℝ)^5207 ≤ (4406203470217/10000000000000 : ℝ)^4183 := by
    have hnat : (517680999 : ℕ)^5207*10000000000000^4183 ≤ 4406203470217^4183*1000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517680999 1000000000 4406203470217 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035362113/2000000000 : ℝ)^5207 ≤ (4406204079431/10000000000000 : ℝ)^4183 := by
    have hnat : (1035362113 : ℕ)^5207*10000000000000^4183 ≤ 4406204079431^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035362113 2000000000 4406204079431 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-902842103/5000000000 : ℝ), (517680999/1000000000 : ℝ), (1035362113/2000000000 : ℝ)] ![(11875924488089/100000000000000 : ℝ), (4406203470217/10000000000000 : ℝ), (4406204079431/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-902842103/5000000000 : ℝ)|^5207 ≤ (11875924488089/100000000000000 : ℝ)^4183
        have hw : |(-902842103/5000000000 : ℝ)|=(902842103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517680999/1000000000 : ℝ)|^5207 ≤ (4406203470217/10000000000000 : ℝ)^4183
        have hw : |(517680999/1000000000 : ℝ)|=(517680999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035362113/2000000000 : ℝ)|^5207 ≤ (4406204079431/10000000000000 : ℝ)^4183
        have hw : |(1035362113/2000000000 : ℝ)|=(1035362113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_5 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393768163/10000000000 : ℝ)*x 0 + (-379405009/2500000000 : ℝ)*x 1 + (2588405013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393768163/10000000000 : ℝ)^5207 ≤ (23186190851653/50000000000000 : ℝ)^4183 := by
    have hnat : (5393768163 : ℕ)^5207*50000000000000^4183 ≤ 23186190851653^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393768163 10000000000 23186190851653 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379405009/2500000000 : ℝ)^5207 ≤ (9565583198187/100000000000000 : ℝ)^4183 := by
    have hnat : (379405009 : ℕ)^5207*100000000000000^4183 ≤ 9565583198187^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379405009 2500000000 9565583198187 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588405013/5000000000 : ℝ)^5207 ≤ (44062035083591/100000000000000 : ℝ)^4183 := by
    have hnat : (2588405013 : ℕ)^5207*100000000000000^4183 ≤ 44062035083591^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588405013 5000000000 44062035083591 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393768163/10000000000 : ℝ), (-379405009/2500000000 : ℝ), (2588405013/5000000000 : ℝ)] ![(23186190851653/50000000000000 : ℝ), (9565583198187/100000000000000 : ℝ), (44062035083591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393768163/10000000000 : ℝ)|^5207 ≤ (23186190851653/50000000000000 : ℝ)^4183
        have hw : |(5393768163/10000000000 : ℝ)|=(5393768163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379405009/2500000000 : ℝ)|^5207 ≤ (9565583198187/100000000000000 : ℝ)^4183
        have hw : |(-379405009/2500000000 : ℝ)|=(379405009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588405013/5000000000 : ℝ)|^5207 ≤ (44062035083591/100000000000000 : ℝ)^4183
        have hw : |(2588405013/5000000000 : ℝ)|=(2588405013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_6 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696884057/5000000000 : ℝ)*x 0 + (1294202549/2500000000 : ℝ)*x 1 + (-1517619873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696884057/5000000000 : ℝ)^5207 ≤ (23186190589453/50000000000000 : ℝ)^4183 := by
    have hnat : (2696884057 : ℕ)^5207*50000000000000^4183 ≤ 23186190589453^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696884057 5000000000 23186190589453 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294202549/2500000000 : ℝ)^5207 ≤ (22031018442373/50000000000000 : ℝ)^4183 := by
    have hnat : (1294202549 : ℕ)^5207*50000000000000^4183 ≤ 22031018442373^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294202549 2500000000 22031018442373 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1517619873/10000000000 : ℝ)^5207 ≤ (956558191929/10000000000000 : ℝ)^4183 := by
    have hnat : (1517619873 : ℕ)^5207*10000000000000^4183 ≤ 956558191929^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517619873 10000000000 956558191929 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696884057/5000000000 : ℝ), (1294202549/2500000000 : ℝ), (-1517619873/10000000000 : ℝ)] ![(23186190589453/50000000000000 : ℝ), (22031018442373/50000000000000 : ℝ), (956558191929/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696884057/5000000000 : ℝ)|^5207 ≤ (23186190589453/50000000000000 : ℝ)^4183
        have hw : |(2696884057/5000000000 : ℝ)|=(2696884057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294202549/2500000000 : ℝ)|^5207 ≤ (22031018442373/50000000000000 : ℝ)^4183
        have hw : |(1294202549/2500000000 : ℝ)|=(1294202549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1517619873/10000000000 : ℝ)|^5207 ≤ (956558191929/10000000000000 : ℝ)^4183
        have hw : |(-1517619873/10000000000 : ℝ)|=(1517619873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_7 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (930540643/2500000000 : ℝ)*x 0 + (4340920959/10000000000 : ℝ)*x 1 + (21704599/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (930540643/2500000000 : ℝ)^5207 ≤ (3652884035487/12500000000000 : ℝ)^4183 := by
    have hnat : (930540643 : ℕ)^5207*12500000000000^4183 ≤ 3652884035487^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930540643 2500000000 3652884035487 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4340920959/10000000000 : ℝ)^5207 ≤ (3538846973049/10000000000000 : ℝ)^4183 := by
    have hnat : (4340920959 : ℕ)^5207*10000000000000^4183 ≤ 3538846973049^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340920959 10000000000 3538846973049 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21704599/50000000 : ℝ)^5207 ≤ (35388457968981/100000000000000 : ℝ)^4183 := by
    have hnat : (21704599 : ℕ)^5207*100000000000000^4183 ≤ 35388457968981^4183*50000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21704599 50000000 35388457968981 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(930540643/2500000000 : ℝ), (4340920959/10000000000 : ℝ), (21704599/50000000 : ℝ)] ![(3652884035487/12500000000000 : ℝ), (3538846973049/10000000000000 : ℝ), (35388457968981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(930540643/2500000000 : ℝ)|^5207 ≤ (3652884035487/12500000000000 : ℝ)^4183
        have hw : |(930540643/2500000000 : ℝ)|=(930540643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4340920959/10000000000 : ℝ)|^5207 ≤ (3538846973049/10000000000000 : ℝ)^4183
        have hw : |(4340920959/10000000000 : ℝ)|=(4340920959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21704599/50000000 : ℝ)|^5207 ≤ (35388457968981/100000000000000 : ℝ)^4183
        have hw : |(21704599/50000000 : ℝ)|=(21704599/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_8 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-830108113/5000000000 : ℝ)*x 0 + (999047961/2000000000 : ℝ)*x 1 + (2733453247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (830108113/5000000000 : ℝ)^5207 ≤ (2139393435027/20000000000000 : ℝ)^4183 := by
    have hnat : (830108113 : ℕ)^5207*20000000000000^4183 ≤ 2139393435027^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830108113 5000000000 2139393435027 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999047961/2000000000 : ℝ)^5207 ≤ (42146626577573/100000000000000 : ℝ)^4183 := by
    have hnat : (999047961 : ℕ)^5207*100000000000000^4183 ≤ 42146626577573^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999047961 2000000000 42146626577573 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733453247/5000000000 : ℝ)^5207 ≤ (9431281247507/20000000000000 : ℝ)^4183 := by
    have hnat : (2733453247 : ℕ)^5207*20000000000000^4183 ≤ 9431281247507^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733453247 5000000000 9431281247507 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-830108113/5000000000 : ℝ), (999047961/2000000000 : ℝ), (2733453247/5000000000 : ℝ)] ![(2139393435027/20000000000000 : ℝ), (42146626577573/100000000000000 : ℝ), (9431281247507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-830108113/5000000000 : ℝ)|^5207 ≤ (2139393435027/20000000000000 : ℝ)^4183
        have hw : |(-830108113/5000000000 : ℝ)|=(830108113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999047961/2000000000 : ℝ)|^5207 ≤ (42146626577573/100000000000000 : ℝ)^4183
        have hw : |(999047961/2000000000 : ℝ)|=(999047961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733453247/5000000000 : ℝ)|^5207 ≤ (9431281247507/20000000000000 : ℝ)^4183
        have hw : |(2733453247/5000000000 : ℝ)|=(2733453247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_9 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196472903/10000000000 : ℝ)*x 0 + (-347445393/2500000000 : ℝ)*x 1 + (17084083/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196472903/10000000000 : ℝ)^5207 ≤ (44270460542797/100000000000000 : ℝ)^4183 := by
    have hnat : (5196472903 : ℕ)^5207*100000000000000^4183 ≤ 44270460542797^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196472903 10000000000 44270460542797 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347445393/2500000000 : ℝ)^5207 ≤ (1714626500799/20000000000000 : ℝ)^4183 := by
    have hnat : (347445393 : ℕ)^5207*20000000000000^4183 ≤ 1714626500799^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347445393 2500000000 1714626500799 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17084083/31250000 : ℝ)^5207 ≤ (47156406946203/100000000000000 : ℝ)^4183 := by
    have hnat : (17084083 : ℕ)^5207*100000000000000^4183 ≤ 47156406946203^4183*31250000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17084083 31250000 47156406946203 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196472903/10000000000 : ℝ), (-347445393/2500000000 : ℝ), (17084083/31250000 : ℝ)] ![(44270460542797/100000000000000 : ℝ), (1714626500799/20000000000000 : ℝ), (47156406946203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196472903/10000000000 : ℝ)|^5207 ≤ (44270460542797/100000000000000 : ℝ)^4183
        have hw : |(5196472903/10000000000 : ℝ)|=(5196472903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347445393/2500000000 : ℝ)|^5207 ≤ (1714626500799/20000000000000 : ℝ)^4183
        have hw : |(-347445393/2500000000 : ℝ)|=(347445393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17084083/31250000 : ℝ)|^5207 ≤ (47156406946203/100000000000000 : ℝ)^4183
        have hw : |(17084083/31250000 : ℝ)|=(17084083/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_10 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598237373/5000000000 : ℝ)*x 0 + (1093380973/2000000000 : ℝ)*x 1 + (-277956279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598237373/5000000000 : ℝ)^5207 ≤ (22135240043781/50000000000000 : ℝ)^4183 := by
    have hnat : (2598237373 : ℕ)^5207*50000000000000^4183 ≤ 22135240043781^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598237373 5000000000 22135240043781 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093380973/2000000000 : ℝ)^5207 ≤ (23578194373163/50000000000000 : ℝ)^4183 := by
    have hnat : (1093380973 : ℕ)^5207*50000000000000^4183 ≤ 23578194373163^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093380973 2000000000 23578194373163 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277956279/2000000000 : ℝ)^5207 ≤ (171462622897/2000000000000 : ℝ)^4183 := by
    have hnat : (277956279 : ℕ)^5207*2000000000000^4183 ≤ 171462622897^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277956279 2000000000 171462622897 2000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598237373/5000000000 : ℝ), (1093380973/2000000000 : ℝ), (-277956279/2000000000 : ℝ)] ![(22135240043781/50000000000000 : ℝ), (23578194373163/50000000000000 : ℝ), (171462622897/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598237373/5000000000 : ℝ)|^5207 ≤ (22135240043781/50000000000000 : ℝ)^4183
        have hw : |(2598237373/5000000000 : ℝ)|=(2598237373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093380973/2000000000 : ℝ)|^5207 ≤ (23578194373163/50000000000000 : ℝ)^4183
        have hw : |(1093380973/2000000000 : ℝ)|=(1093380973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277956279/2000000000 : ℝ)|^5207 ≤ (171462622897/2000000000000 : ℝ)^4183
        have hw : |(-277956279/2000000000 : ℝ)|=(277956279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_11 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (927111819/2000000000 : ℝ)*x 0 + (970632379/2500000000 : ℝ)*x 1 + (1941268411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (927111819/2000000000 : ℝ)^5207 ≤ (3840287985979/10000000000000 : ℝ)^4183 := by
    have hnat : (927111819 : ℕ)^5207*10000000000000^4183 ≤ 3840287985979^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927111819 2000000000 3840287985979 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970632379/2500000000 : ℝ)^5207 ≤ (30798523991923/100000000000000 : ℝ)^4183 := by
    have hnat : (970632379 : ℕ)^5207*100000000000000^4183 ≤ 30798523991923^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970632379 2500000000 30798523991923 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1941268411/5000000000 : ℝ)^5207 ≤ (30798596134993/100000000000000 : ℝ)^4183 := by
    have hnat : (1941268411 : ℕ)^5207*100000000000000^4183 ≤ 30798596134993^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941268411 5000000000 30798596134993 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(927111819/2000000000 : ℝ), (970632379/2500000000 : ℝ), (1941268411/5000000000 : ℝ)] ![(3840287985979/10000000000000 : ℝ), (30798523991923/100000000000000 : ℝ), (30798596134993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(927111819/2000000000 : ℝ)|^5207 ≤ (3840287985979/10000000000000 : ℝ)^4183
        have hw : |(927111819/2000000000 : ℝ)|=(927111819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(970632379/2500000000 : ℝ)|^5207 ≤ (30798523991923/100000000000000 : ℝ)^4183
        have hw : |(970632379/2500000000 : ℝ)|=(970632379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1941268411/5000000000 : ℝ)|^5207 ≤ (30798596134993/100000000000000 : ℝ)^4183
        have hw : |(1941268411/5000000000 : ℝ)|=(1941268411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_12 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-634408071/5000000000 : ℝ)*x 0 + (1119279903/2000000000 : ℝ)*x 1 + (1287892669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (634408071/5000000000 : ℝ)^5207 ≤ (7654385884737/100000000000000 : ℝ)^4183 := by
    have hnat : (634408071 : ℕ)^5207*100000000000000^4183 ≤ 7654385884737^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634408071 5000000000 7654385884737 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119279903/2000000000 : ℝ)^5207 ≤ (6068853852719/12500000000000 : ℝ)^4183 := by
    have hnat : (1119279903 : ℕ)^5207*12500000000000^4183 ≤ 6068853852719^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119279903 2000000000 6068853852719 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287892669/2500000000 : ℝ)^5207 ≤ (43794783283957/100000000000000 : ℝ)^4183 := by
    have hnat : (1287892669 : ℕ)^5207*100000000000000^4183 ≤ 43794783283957^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287892669 2500000000 43794783283957 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-634408071/5000000000 : ℝ), (1119279903/2000000000 : ℝ), (1287892669/2500000000 : ℝ)] ![(7654385884737/100000000000000 : ℝ), (6068853852719/12500000000000 : ℝ), (43794783283957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-634408071/5000000000 : ℝ)|^5207 ≤ (7654385884737/100000000000000 : ℝ)^4183
        have hw : |(-634408071/5000000000 : ℝ)|=(634408071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119279903/2000000000 : ℝ)|^5207 ≤ (6068853852719/12500000000000 : ℝ)^4183
        have hw : |(1119279903/2000000000 : ℝ)|=(1119279903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287892669/2500000000 : ℝ)|^5207 ≤ (43794783283957/100000000000000 : ℝ)^4183
        have hw : |(1287892669/2500000000 : ℝ)|=(1287892669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_13 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082192631/2000000000 : ℝ)*x 0 + (-764104481/5000000000 : ℝ)*x 1 + (5151571331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082192631/2000000000 : ℝ)^5207 ≤ (9311295011643/20000000000000 : ℝ)^4183 := by
    have hnat : (1082192631 : ℕ)^5207*20000000000000^4183 ≤ 9311295011643^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082192631 2000000000 9311295011643 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (764104481/5000000000 : ℝ)^5207 ≤ (2412183676061/25000000000000 : ℝ)^4183 := by
    have hnat : (764104481 : ℕ)^5207*25000000000000^4183 ≤ 2412183676061^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764104481 5000000000 2412183676061 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151571331/10000000000 : ℝ)^5207 ≤ (21897395107701/50000000000000 : ℝ)^4183 := by
    have hnat : (5151571331 : ℕ)^5207*50000000000000^4183 ≤ 21897395107701^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151571331 10000000000 21897395107701 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082192631/2000000000 : ℝ), (-764104481/5000000000 : ℝ), (5151571331/10000000000 : ℝ)] ![(9311295011643/20000000000000 : ℝ), (2412183676061/25000000000000 : ℝ), (21897395107701/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082192631/2000000000 : ℝ)|^5207 ≤ (9311295011643/20000000000000 : ℝ)^4183
        have hw : |(1082192631/2000000000 : ℝ)|=(1082192631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-764104481/5000000000 : ℝ)|^5207 ≤ (2412183676061/25000000000000 : ℝ)^4183
        have hw : |(-764104481/5000000000 : ℝ)|=(764104481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151571331/10000000000 : ℝ)|^5207 ≤ (21897395107701/50000000000000 : ℝ)^4183
        have hw : |(5151571331/10000000000 : ℝ)|=(5151571331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_14 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410964231/10000000000 : ℝ)*x 0 + (1030313999/2000000000 : ℝ)*x 1 + (-305641859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410964231/10000000000 : ℝ)^5207 ≤ (23278243291297/50000000000000 : ℝ)^4183 := by
    have hnat : (5410964231 : ℕ)^5207*50000000000000^4183 ≤ 23278243291297^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410964231 10000000000 23278243291297 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030313999/2000000000 : ℝ)^5207 ≤ (10948694019343/25000000000000 : ℝ)^4183 := by
    have hnat : (1030313999 : ℕ)^5207*25000000000000^4183 ≤ 10948694019343^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030313999 2000000000 10948694019343 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305641859/2000000000 : ℝ)^5207 ≤ (2412184330353/25000000000000 : ℝ)^4183 := by
    have hnat : (305641859 : ℕ)^5207*25000000000000^4183 ≤ 2412184330353^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305641859 2000000000 2412184330353 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410964231/10000000000 : ℝ), (1030313999/2000000000 : ℝ), (-305641859/2000000000 : ℝ)] ![(23278243291297/50000000000000 : ℝ), (10948694019343/25000000000000 : ℝ), (2412184330353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410964231/10000000000 : ℝ)|^5207 ≤ (23278243291297/50000000000000 : ℝ)^4183
        have hw : |(5410964231/10000000000 : ℝ)|=(5410964231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030313999/2000000000 : ℝ)|^5207 ≤ (10948694019343/25000000000000 : ℝ)^4183
        have hw : |(1030313999/2000000000 : ℝ)|=(1030313999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-305641859/2000000000 : ℝ)|^5207 ≤ (2412184330353/25000000000000 : ℝ)^4183
        have hw : |(-305641859/2000000000 : ℝ)|=(305641859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_box_15 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3639272297/10000000000 : ℝ)*x 0 + (547585217/1250000000 : ℝ)*x 1 + (547584883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3639272297/10000000000 : ℝ)^5207 ≤ (14207600936869/50000000000000 : ℝ)^4183 := by
    have hnat : (3639272297 : ℕ)^5207*50000000000000^4183 ≤ 14207600936869^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3639272297 10000000000 14207600936869 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547585217/1250000000 : ℝ)^5207 ≤ (35792412641487/100000000000000 : ℝ)^4183 := by
    have hnat : (547585217 : ℕ)^5207*100000000000000^4183 ≤ 35792412641487^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547585217 1250000000 35792412641487 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547584883/1250000000 : ℝ)^5207 ≤ (7158477093099/20000000000000 : ℝ)^4183 := by
    have hnat : (547584883 : ℕ)^5207*20000000000000^4183 ≤ 7158477093099^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547584883 1250000000 7158477093099 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3639272297/10000000000 : ℝ), (547585217/1250000000 : ℝ), (547584883/1250000000 : ℝ)] ![(14207600936869/50000000000000 : ℝ), (35792412641487/100000000000000 : ℝ), (7158477093099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3639272297/10000000000 : ℝ)|^5207 ≤ (14207600936869/50000000000000 : ℝ)^4183
        have hw : |(3639272297/10000000000 : ℝ)|=(3639272297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547585217/1250000000 : ℝ)|^5207 ≤ (35792412641487/100000000000000 : ℝ)^4183
        have hw : |(547585217/1250000000 : ℝ)|=(547585217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547584883/1250000000 : ℝ)|^5207 ≤ (7158477093099/20000000000000 : ℝ)^4183
        have hw : |(547584883/1250000000 : ℝ)|=(547584883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1698_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8589/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2477/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66639/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1453/2500 : ℝ) ∧ (40541/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (361/400 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8589/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2477/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8589/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2477/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8589/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2477/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8589/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2477/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8589/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2477/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8589/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2477/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2477/25000 : ℝ) ^ (5199/1024 : ℝ) ≤ (99857776397097/12500000000000000000 : ℝ) := by
    have hpowers : (2477/25000 : ℝ)^5199 ≤ (99857776397097/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2477 : ℕ)^5199*12500000000000000000^1024 ≤ 99857776397097^1024*25000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2477 25000 99857776397097 12500000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2477/25000 : ℝ)) (X := (99857776397097/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8589/50000 : ℝ) ^ (5199/1024 : ℝ) ≤ (13056967507019253/100000000000000000000 : ℝ) := by
    have hpowers : (8589/50000 : ℝ)^5199 ≤ (13056967507019253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8589 : ℕ)^5199*100000000000000000000^1024 ≤ 13056967507019253^1024*50000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8589 50000 13056967507019253 100000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8589/50000 : ℝ)) (X := (13056967507019253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250099857776397097/6250000000000000000 : ℝ) ≤ (5000015734365387/5000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (6250099857776397097/6250000000000000000 : ℝ)^1024 ≤ (5000015734365387/5000000000000000 : ℝ)^5199 := by
      have hnat : (6250099857776397097 : ℕ)^1024*5000000000000000^5199 ≤ 5000015734365387^5199*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250099857776397097 6250000000000000000 5000015734365387 5000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015734365387/5000000000000000 : ℝ)) (X := (6250099857776397097/6250000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013855829718196029/100000000000000000000 : ℝ) ≤ (10000272890562481/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (100013855829718196029/100000000000000000000 : ℝ)^1024 ≤ (10000272890562481/10000000000000000 : ℝ)^5199 := by
      have hnat : (100013855829718196029 : ℕ)^1024*10000000000000000^5199 ≤ 10000272890562481^5199*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013855829718196029 100000000000000000000 10000272890562481 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000272890562481/10000000000000000 : ℝ)) (X := (100013855829718196029/100000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013056967507019253/50000000000000000000 : ℝ) ≤ (2500128578098547/2500000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (50013056967507019253/50000000000000000000 : ℝ)^1024 ≤ (2500128578098547/2500000000000000 : ℝ)^5199 := by
      have hnat : (50013056967507019253 : ℕ)^1024*2500000000000000^5199 ≤ 2500128578098547^5199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013056967507019253 50000000000000000000 2500128578098547 2500000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500128578098547/2500000000000000 : ℝ)) (X := (50013056967507019253/50000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(99857776397097/12500000000000000000 : ℝ) ≤ ((18173861190663905267/18175000000000000000 : ℝ)+2*(241421831707/727000000000000 : ℝ)*(2477/25000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (18173861190663905267/18175000000000000000 : ℝ)+2*(241421831707/727000000000000 : ℝ)*(2477/25000 : ℝ)=(5000015734365387/5000000000000000 : ℝ) by norm_num, show 1+2*(99857776397097/12500000000000000000 : ℝ)=(6250099857776397097/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13056967507019253/100000000000000000000 : ℝ)+(99857776397097/12500000000000000000 : ℝ) ≤ ((18173861190663905267/18175000000000000000 : ℝ)+(241421831707/727000000000000 : ℝ)*((8589/50000 : ℝ)+(2477/25000 : ℝ)))^(5199/1024 : ℝ) := by
    rw [show (18173861190663905267/18175000000000000000 : ℝ)+(241421831707/727000000000000 : ℝ)*((8589/50000 : ℝ)+(2477/25000 : ℝ))=(10000272890562481/10000000000000000 : ℝ) by norm_num, show 1+(13056967507019253/100000000000000000000 : ℝ)+(99857776397097/12500000000000000000 : ℝ)=(100013855829718196029/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13056967507019253/100000000000000000000 : ℝ) ≤ ((18173861190663905267/18175000000000000000 : ℝ)+2*(241421831707/727000000000000 : ℝ)*(8589/50000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (18173861190663905267/18175000000000000000 : ℝ)+2*(241421831707/727000000000000 : ℝ)*(8589/50000 : ℝ)=(2500128578098547/2500000000000000 : ℝ) by norm_num, show 1+2*(13056967507019253/100000000000000000000 : ℝ)=(50013056967507019253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18173861190663905267/18175000000000000000 : ℝ)*(X 1 0+X 2 0)+(241421831707/727000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (2477/25000 : ℝ)) (hi := (8589/50000 : ℝ)) (c := (18173861190663905267/18175000000000000000 : ℝ)) (alpha := (241421831707/727000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18173861190663905267/18175000000000000000 : ℝ)*(X 0 1+X 2 1)+(241421831707/727000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (2477/25000 : ℝ)) (hi := (8589/50000 : ℝ)) (c := (18173861190663905267/18175000000000000000 : ℝ)) (alpha := (241421831707/727000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18173861190663905267/18175000000000000000 : ℝ)*(X 0 2+X 1 2)+(241421831707/727000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (2477/25000 : ℝ)) (hi := (8589/50000 : ℝ)) (c := (18173861190663905267/18175000000000000000 : ℝ)) (alpha := (241421831707/727000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1128433451/10000000000 : ℝ)*X 0 0+(1355916413/2500000000 : ℝ)*X 0 1+(1355916377/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612934079/5000000000 : ℝ)*X 1 0+(-704764391/5000000000 : ℝ)*X 1 1+(5423665513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612934081/5000000000 : ℝ)*X 2 0+(1355916383/2500000000 : ℝ)*X 2 1+(-1409528749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4503672913/10000000000 : ℝ)*X 0 0+(3951012149/10000000000 : ℝ)*X 0 1+(3951012139/10000000000 : ℝ)*X 0 2+(4503672913/10000000000 : ℝ)*X 1 0+(3951012149/10000000000 : ℝ)*X 1 1+(3951012139/10000000000 : ℝ)*X 1 2+(4503672913/10000000000 : ℝ)*X 2 0+(3951012149/10000000000 : ℝ)*X 2 1+(3951012139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-902842103/5000000000 : ℝ)*X 0 0+(517680999/1000000000 : ℝ)*X 0 1+(1035362113/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5393768163/10000000000 : ℝ)*X 1 0+(-379405009/2500000000 : ℝ)*X 1 1+(2588405013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2696884057/5000000000 : ℝ)*X 2 0+(1294202549/2500000000 : ℝ)*X 2 1+(-1517619873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((930540643/2500000000 : ℝ)*X 0 0+(4340920959/10000000000 : ℝ)*X 0 1+(21704599/50000000 : ℝ)*X 0 2+(930540643/2500000000 : ℝ)*X 1 0+(4340920959/10000000000 : ℝ)*X 1 1+(21704599/50000000 : ℝ)*X 1 2+(930540643/2500000000 : ℝ)*X 2 0+(4340920959/10000000000 : ℝ)*X 2 1+(21704599/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-830108113/5000000000 : ℝ)*X 0 0+(999047961/2000000000 : ℝ)*X 0 1+(2733453247/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196472903/10000000000 : ℝ)*X 1 0+(-347445393/2500000000 : ℝ)*X 1 1+(17084083/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598237373/5000000000 : ℝ)*X 2 0+(1093380973/2000000000 : ℝ)*X 2 1+(-277956279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((927111819/2000000000 : ℝ)*X 0 0+(970632379/2500000000 : ℝ)*X 0 1+(1941268411/5000000000 : ℝ)*X 0 2+(927111819/2000000000 : ℝ)*X 1 0+(970632379/2500000000 : ℝ)*X 1 1+(1941268411/5000000000 : ℝ)*X 1 2+(927111819/2000000000 : ℝ)*X 2 0+(970632379/2500000000 : ℝ)*X 2 1+(1941268411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-634408071/5000000000 : ℝ)*X 0 0+(1119279903/2000000000 : ℝ)*X 0 1+(1287892669/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1082192631/2000000000 : ℝ)*X 1 0+(-764104481/5000000000 : ℝ)*X 1 1+(5151571331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5410964231/10000000000 : ℝ)*X 2 0+(1030313999/2000000000 : ℝ)*X 2 1+(-305641859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3639272297/10000000000 : ℝ)*X 0 0+(547585217/1250000000 : ℝ)*X 0 1+(547584883/1250000000 : ℝ)*X 0 2+(3639272297/10000000000 : ℝ)*X 1 0+(547585217/1250000000 : ℝ)*X 1 1+(547584883/1250000000 : ℝ)*X 1 2+(3639272297/10000000000 : ℝ)*X 2 0+(547585217/1250000000 : ℝ)*X 2 1+(547584883/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66639/100000 : ℝ) ≤ (-37847516285704129106809960493769/56796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19910801/25000000000000 : ℝ)*(upper1) + (16612113/100000000000000 : ℝ)*(lower2) + (14743427/100000000000000 : ℝ)*(upper5) + (165761875371431/12500000000000 : ℝ)*(major0) + (165761875371431/12500000000000 : ℝ)*(major1) + (165761875371431/12500000000000 : ℝ)*(major2) + (1063947549/100000000000000 : ℝ)*(sp1) + (396022160771397/20000000000000 : ℝ)*(sp4) + (495027516263019/25000000000000 : ℝ)*(sp5) + (495026553632739/25000000000000 : ℝ)*(sp6) + (347136382658843/50000000000000 : ℝ)*(sp7) + (4064283/1250000000000 : ℝ)*(sp12) + (4914468669/100000000000000 : ℝ)*(sp14) + (18317423703/100000000000000 : ℝ)*(sp15) + (694291082741389/100000000000000 : ℝ)*(f.failure) + (15840889031997/800000000000 : ℝ)*(f.sum) + (26386678841907/18175000000000000000000000000 : ℝ)*base66 + (673713646017347923/227187500000000000000000000000000 : ℝ)*base68 + (568489239290785423/227187500000000000000000000000000 : ℝ)*base70 + (990852919857035423/227187500000000000000000000000000 : ℝ)*base72 + (1184554942623/1135937500000000000000000000 : ℝ)*base73 + (348707490179214577/227187500000000000000000000000000 : ℝ)*base75 + (1377256689766722923/227187500000000000000000000000000 : ℝ)*base78 + (602220984232035423/227187500000000000000000000000000 : ℝ)*base80 + (65041941545293/18175000000000000000000000000 : ℝ)*base81 + (2053071/10000000000000000000000 : ℝ)*base90 + (2053071/10000000000000000000000 : ℝ)*base92 + (2053071/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (1453/2500 : ℝ) ≤ (21127504808417902365095037273/36350000000000000000000000000 : ℝ) := by norm_num
    linear_combination (470029/20000000000000 : ℝ)*(upper0) + (121511/100000000000000 : ℝ)*(lower1) + (1619889/25000000000000 : ℝ)*(upper4) + (1427437800894571/100000000000000 : ℝ)*(major0) + (1427437800894571/100000000000000 : ℝ)*(major1) + (1427437800894571/100000000000000 : ℝ)*(major2) + (52203765056517/2500000000000 : ℝ)*(sp0) + (2088150815615559/100000000000000 : ℝ)*(sp1) + (65254719506667/3125000000000 : ℝ)*(sp2) + (747349864200301/100000000000000 : ℝ)*(sp3) + (127502239/50000000000000 : ℝ)*(sp6) + (78414757/25000000000000 : ℝ)*(sp7) + (338478571/50000000000000 : ℝ)*(sp8) + (57950283/12500000000000 : ℝ)*(sp9) + (747350177859329/100000000000000 : ℝ)*(f.failure) + (2088151279217823/100000000000000 : ℝ)*(f.sum) + (109719463009253/36350000000000000000000000000 : ℝ)*base66 + (7094488480273530457/1817500000000000000000000000000000 : ℝ)*base67 + (611668711493530457/1817500000000000000000000000000000 : ℝ)*base69 + (11650378052336469543/1817500000000000000000000000000000 : ℝ)*base72 + (106825003311553/36350000000000000000000000000 : ℝ)*base74 + (8124804825538969543/1817500000000000000000000000000000 : ℝ)*base76 + (13293272740508530457/1817500000000000000000000000000000 : ℝ)*base77 + (24420445396981469543/1817500000000000000000000000000000 : ℝ)*base80 + (89928205042453/36350000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (16553269/10000000000000000000000 : ℝ)*base89 + (16553269/10000000000000000000000 : ℝ)*base91 + (16553269/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40541/50000 : ℝ) ≤ (589486378169709813662404319649/727000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149818397/100000000000000 : ℝ)*(upper0) + (134316281/100000000000000 : ℝ)*(lower1) + (65094161/10000000000000 : ℝ)*(lower3) + (15761107/20000000000000 : ℝ)*(lower5) + (2326875042051/160000000000 : ℝ)*(major0) + (2326875042051/160000000000 : ℝ)*(major1) + (2326875042051/160000000000 : ℝ)*(major2) + (5107967221/50000000000000 : ℝ)*(sp0) + (132927643399/100000000000000 : ℝ)*(sp1) + (53266800271/100000000000000 : ℝ)*(sp3) + (1060071390524149/50000000000000 : ℝ)*(sp8) + (106001003466967/5000000000000 : ℝ)*(sp9) + (106007649849137/5000000000000 : ℝ)*(sp10) + (380679638758323/50000000000000 : ℝ)*(sp11) + (761412544316917/100000000000000 : ℝ)*(f.failure) + (106007649849137/5000000000000 : ℝ)*(f.sum) + (878564181337/1454000000000000000000000000 : ℝ)*base66 + (3621025463395617/2908000000000000000000000000000 : ℝ)*base67 + (17696936981724383/2908000000000000000000000000000 : ℝ)*base70 + (22092804119467617/2908000000000000000000000000000 : ℝ)*base71 + (27379911341093/1454000000000000000000000000 : ℝ)*base74 + (26789660572463617/2908000000000000000000000000000 : ℝ)*base75 + (9376146355443617/2908000000000000000000000000000 : ℝ)*base77 + (10394507651787617/2908000000000000000000000000000 : ℝ)*base79 + (8405128701549/1454000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (13051463/10000000000000000000000 : ℝ)*base90 + (13051463/10000000000000000000000 : ℝ)*base92 + (13051463/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-361/400 : ℝ) ≤ (-410062010392924977197752620650133/454375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2339651/25000000000000 : ℝ)*(lower0) + (158518641/100000000000000 : ℝ)*(lower2) + (112157701/50000000000000 : ℝ)*(upper3) + (1502245750531233/100000000000000 : ℝ)*(major0) + (1502245750531233/100000000000000 : ℝ)*(major1) + (1502245750531233/100000000000000 : ℝ)*(major2) + (808255253/100000000000000 : ℝ)*(sp0) + (39249198491/100000000000000 : ℝ)*(sp5) + (87729859347/100000000000000 : ℝ)*(sp6) + (2802275909/12500000000000 : ℝ)*(sp7) + (224805651569727/10000000000000 : ℝ)*(sp12) + (140501129672127/6250000000000 : ℝ)*(sp13) + (2247969594093177/100000000000000 : ℝ)*(sp14) + (786494253933779/100000000000000 : ℝ)*(sp15) + (786516672141051/100000000000000 : ℝ)*(f.failure) + (562014330988131/25000000000000 : ℝ)*(f.sum) + (74809011834331/36350000000000000000000000000 : ℝ)*base65 + (12186501703889979211/1817500000000000000000000000000000 : ℝ)*base67 + (11166541965004979211/1817500000000000000000000000000000 : ℝ)*base69 + (18341086065304979211/1817500000000000000000000000000000 : ℝ)*base71 + (657582791953469/36350000000000000000000000000 : ℝ)*base74 + (11857992911809979211/1817500000000000000000000000000000 : ℝ)*base75 + (10492247843794979211/1817500000000000000000000000000000 : ℝ)*base77 + (16172736176027520789/1817500000000000000000000000000000 : ℝ)*base80 + (98804469813769/36350000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13393911/10000000000000000000000 : ℝ)*base89 + (13393911/10000000000000000000000 : ℝ)*base91 + (13393911/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1698_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8589/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2477/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66639/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1453/2500 : ℝ) else (40541/50000 : ℝ) ≤ X j i ∧ X j i ≤ (361/400 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1698_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1698_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66639/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1453/2500 : ℝ) else (40541/50000 : ℝ) ≤ X j i ∧ X j i ≤ (361/400 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1698_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1698_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1698_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66639/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1453/2500 : ℝ) else (40541/50000 : ℝ) ≤ X j i ∧ X j i ≤ (361/400 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1698_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
